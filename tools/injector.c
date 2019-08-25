/*
    Generates data frames at every MCS value across 20 and 40mhz
    for testing tx and rx.

    Allows tagging packets with location info for site surveys.

    Packets are sent as beacons encoded at different MCS rates; 
    beacons SHOULD bypass the triggering of CTS/RTS frame control.

    Packets are sent with 2 custom IE tags:

    ie 10, length 14
        Packed byte field encoding:

            Byte 0 - MCS rate and flags, where
                Bit 7 indicates HT40 mode
                Bit 6 indicates ShortGI mode
                Bits 0-3 indicate MCS values 0-15
            Byte 1 - Location code (0-255)
            Bytes 2-5
                32 bit current packet count
            Bytes 6-9
                32 bit maximum packet count
            Bytes 10-13
                32 bit random session id

    ie 11, length 64
        Text field containing a text description of the packed field
*/

#include <stdio.h>
#include <getopt.h>
#include <string.h>
#include <sys/time.h>
#include <arpa/inet.h>

#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <termios.h>
#include <pthread.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/select.h>
#include <netdb.h>

#include <stdbool.h>

#include <lorcon2/csi_func.h>
#include <lorcon2/lorcon.h>
#include <lorcon2/lorcon_forge.h>
#include <lorcon2/lorcon_packasm.h>

/* MCS only goes 0-15 or 4 bits, so we use bits 6 and 7 to indicate if we
 * are sending HT40 and GI */
#define HT_FLAG_40  (1 << 7)
#define HT_FLAG_GI  (1 << 6)

#define csi_st_len 23
#define PAYLOAD_LEN 64
#define BUFSIZE 4096
#define Kernel_CSI_ST_LEN 23 

unsigned char buf_addr[BUFSIZE];
unsigned char data_buf[1500];

int quit;
int sock;
int fd;
int log_flag;
FILE*  fp;
COMPLEX csi_matrix[3][3][114];
csi_struct*   csi_status;
int flag;
struct hostent *hp;
struct sockaddr_in pin;

unsigned int MCS = 0;

// declaration of thread condition variables
pthread_cond_t cond1 = PTHREAD_COND_INITIALIZER;
pthread_cond_t cond2 = PTHREAD_COND_INITIALIZER;
pthread_cond_t cond3 = PTHREAD_COND_INITIALIZER;

// mutex which we are going to use aboid race condition
pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

// gloabl variable which decides which waiting thread should be scheduled
int done = 1;

struct estimator_args {
    char   *hostname;
    int    port;
};

struct injector_args {
    lorcon_t *context;
    lcpa_metapack_t *metapack;
    lorcon_packet_t *txpack;
    int BW;
    int GI;
    unsigned int interval;
    unsigned int npackets;
    unsigned int ttime;
    //uint8_t RA_MAC[6];
    //uint8_t *TA_MAC;
    uint32_t session_id;
};

int open_csi_device(){
   int fd;
   fd = open("/dev/CSI_dev",O_RDWR);
    return fd;
}

void close_csi_device(int fd){
    close(fd);
    remove("/dev/CSI_dev");
}


int read_csi_buf(unsigned char* buf_addr,int fd, int buf_size){
    int cnt;
    /* listen to the port
     * read when 1, a csi is reported from kernel
     *           2, time out
     */
    cnt = read(fd,buf_addr,buf_size);
    printf("cnt: %d \n", cnt);
    if(cnt < 0)
	return 0;
    if(cnt)
        return cnt;
    else
        return 0;
}

void record_status(unsigned char* buf_addr, int cnt, csi_struct* csi_status_tmp){
    int i;
    csi_status_tmp->tstamp  =
         ((buf_addr[0] << 56) & 0x00000000000000ff) | ((buf_addr[1] << 48) & 0x000000000000ff00) |
         ((buf_addr[2] << 40) & 0x0000000000ff0000) | ((buf_addr[3] << 32) & 0x00000000ff000000) |
         ((buf_addr[4] << 24) & 0x000000ff00000000) | ((buf_addr[5] << 16) & 0x0000ff0000000000) |
         ((buf_addr[6] << 8)  & 0x00ff000000000000) | ((buf_addr[7])       & 0xff00000000000000) ;
    csi_status_tmp->csi_len = ((buf_addr[8] << 8) & 0xff00) | (buf_addr[9] & 0x00ff);
    csi_status_tmp->channel = ((buf_addr[10] << 8) & 0xff00) | (buf_addr[11] & 0x00ff);
    csi_status_tmp->buf_len = ((buf_addr[cnt-2] << 8) & 0xff00) | (buf_addr[cnt-1] & 0x00ff);
    csi_status_tmp->payload_len = ((buf_addr[csi_st_len] << 8) & 0xff00) | ((buf_addr[csi_st_len + 1]) & 0x00ff);
    csi_status_tmp->phyerr    = buf_addr[12];
    csi_status_tmp->noise     = buf_addr[13];
    csi_status_tmp->rate      = buf_addr[14];
    csi_status_tmp->chanBW    = buf_addr[15];
    csi_status_tmp->num_tones = buf_addr[16];
    csi_status_tmp->nr        = buf_addr[17];
    csi_status_tmp->nc        = buf_addr[18];

    csi_status_tmp->rssi      = buf_addr[19];
    csi_status_tmp->rssi_0    = buf_addr[20];
    csi_status_tmp->rssi_1    = buf_addr[21];
    csi_status_tmp->rssi_2    = buf_addr[22];
    csi_status_tmp->mac_addr  = buf_addr[csi_st_len + csi_status_tmp->csi_len + 16 + 1];
}


void sig_handler(int signo){
    if(signo == SIGINT){
        quit = 1;
    }
}
void exit_program(){
    printf("!!! WE EXIT !!!\n");
    if (log_flag == 1){
        fclose(fp);
    }
    close(fd);
    close(sock);
    sock = -1;
}

int checkCPUendian(){
    int num = 1;
    if(*((char*)&num) == 1){
        //printf("Little-endian\n");
        return 0;
    }
    else{
        //printf("Big-endian\n");
        return 1;
    }
}

void usage(char *argv[]) {
    printf("\t-i <interface>            Radio interface\n");
    printf("\t-c <channel>              Channel (should be HT40)\n");
    printf("\t-m <MCS_index>            MCS index (0~15)\n");
    printf("\t-b <band_width>           Band width(0-20M | 1-40M)\n");
    printf("\t-g <guard_interval>       Guard interval\n");
    printf("\t-n <number of packets>    Number of packets to send\n");
    printf("\t-t <time_interval>        Transmission delay (m)\n");
    printf("\t-d <delay>                Interpacket delay (us)\n");
    printf("\t-o <hostname>             Hostname\n");
    printf("\t-p <port>                 Server port\n");
    printf("\nExample:\n");
    printf("\t%s -i mon0 -c 6HT20 -m 0 -n 1 -d 1 -o 192.168.1.211 -p 6767 -s 55\n\n", argv[0]);
}

bool isvalueinarray(int val, int *arr, int size){
    int i;
    for (i=0; i<size; i++){
        if (arr[i] == val)
            return true;
    }
    return false;
}

void *estimate_csi(void *n){
    int    total_msg_cnt,cnt;
    int    data_len,data_len_local;
    int    byte_cnt,send_cnt,recv_cnt;
    int    CPUendian;
    int    eMCS;
    int    mac_array[] = {45, 55, 207, 122, 221, 241, 25, 61, 139};

    flag = 0;
    quit = 0;
    printf("# Receiving data! Press Ctrl+c to quit!\n");
    while(quit == 0){    
        if (quit == 1){
            exit_program();
            return 0;
        }

	if (flag == 0){
		//1) send CSI to the server
		cnt = read_csi_buf(buf_addr,fd,BUFSIZE);

		if(cnt){
		    total_msg_cnt += 1;
		    data_len        = cnt;
		    data_len_local  = data_len;

		    CPUendian = checkCPUendian();
		    if(CPUendian == 1){
			unsigned char *tmp = (unsigned char *)&data_len;
			unsigned char t;
			t = tmp[0];tmp[0] = tmp[3];tmp[3] = t;
			t = tmp[1];tmp[1] = tmp[2];tmp[2] = t;
		    }

		    u_int16_t csi_len = ((buf_addr[8] << 8) & 0xff00) | (buf_addr[9] & 0x00ff);
                    u_int8_t mac_addr = buf_addr[csi_st_len + csi_len + 16 + 1];

	            int mac_array_size = (int)(sizeof(mac_array)/sizeof(mac_array[0]));
                    printf("mac_addr is: %d \n",mac_addr);

                    if (isvalueinarray(mac_addr, mac_array, mac_array_size)){
			printf("send CSI to the server \n");
		    	// send the count first
		    	send_cnt  = send(sock,(unsigned char *)&data_len,sizeof(int),0);
		    	if(send_cnt == -1){
				perror("send");
				exit_program();
				return 0;
		    	}
		 
		    	// send the actual data
		    	byte_cnt = 0;
		    	while(byte_cnt < data_len_local){
				send_cnt = send(sock,buf_addr+byte_cnt,data_len_local-byte_cnt,0);
				if(send_cnt == -1){
			    	perror("send");
			    	exit_program();
			    	return 0;
				}
				byte_cnt += send_cnt;
		    	}
		     }
		}
		//recv_cnt = recv(sock, &eMCS, sizeof(eMCS),0);
		//printf("recv_cnt: %d \n", recv_cnt);
		//if(recv_cnt == -1){
		//	perror("recv");    
		//	exit_program();
		//	return 0;
		//}
		//if(recv_cnt > 0)
		//	printf("MCS index received: %d \n ", eMCS); 	
	}
    }
    return NULL;
}

void *update_mcs(void *n){
    int    eMCS;
    int    recv_cnt;
    //printf("update_mcs thread ready\n");

    flag = 0;
    quit = 0;
    while(quit == 0){
        if (quit == 1){
            exit_program();
            return 0;
        }

        if (flag == 0){
                //2) receive and update the MCS index
                //recv_cnt = recv(sock, (unsigned char *)&eMCS, sizeof(eMCS),0);
		char integer[4];
		recv_cnt = recv(sock,integer,4,0);
		//printf("recv_cnt: %d \n", recv_cnt);
                if(recv_cnt == -1){
                    perror("recv");
                    exit_program();
                    return 0;
                }
		//int mcs = eMCS;
                if(recv_cnt > 0)
			printf("MCS index received: %s \n ", integer);
        }
    }
    return NULL;
}


void *inject_data(void *_args){
    int i,tmp;
    unsigned int count, totalcount;
    unsigned int lcode = 0;
    uint8_t fcflags = 3;
    uint8_t fragement = 3;
    uint8_t sequence = 2;
    unsigned int duration = 0;
    uint8_t encoded_payload[14];
    uint32_t *encoded_counter = (uint32_t *) (encoded_payload + 2);
    uint32_t *encoded_max = (uint32_t *) (encoded_payload + 6);
    uint32_t *encoded_session = (uint32_t *) (encoded_payload + 10);
    uint8_t payload[2*PAYLOAD_LEN];
    uint8_t payload_1[PAYLOAD_LEN];
    struct timeval time;
    uint64_t timestamp;

    uint8_t *dmac = "\x04\xF0\x21\x32\xBD\xA5";
    uint8_t *bmac = "\x00\xDE\xAD\xBE\xEF\x00";

    uint8_t RA_MAC[6];
    RA_MAC[0] = 0x04;
    RA_MAC[1] =0xF0;
    RA_MAC[2] =0x21;
    RA_MAC[3] =0x32;
    RA_MAC[4] =0xBD;
    RA_MAC[5] =0xA5;
    uint8_t *TA_MAC;
    uint8_t *DA_MAC = RA_MAC;
    uint8_t *BSSID_MAC = bmac;

    struct injector_args *args = (struct injector_args *) _args;

    lorcon_t *context = args->context;
    lcpa_metapack_t *metapack = args->metapack;
    lorcon_packet_t *txpack = args-> txpack;
    int BW = args->BW;
    int GI = args->GI;
    unsigned int interval = args->interval;
    unsigned int npackets = args->npackets;
    //uint8_t RA_MAC[6] = args->RA_MAC;
    //uint8_t *TA_MAC = args->TA_MAC;
    uint32_t session_id = args->session_id;
    unsigned int ttime = args->ttime;

    while (1){
	    sleep(ttime);
	    //1) disable thread 1 that recv CSI and transfer CSI with the server
	    flag = 1;

	    //2) inject data to AP based on the calculated MCS
	    printf("--------------inject to other clients!--------------\n");
	    for (count = 0; count < npackets; count++) {
		    memset(payload, 0, 2*PAYLOAD_LEN);
		    memset(payload_1, 0, PAYLOAD_LEN);
		    for (i = 0; i < PAYLOAD_LEN; i++){
			    payload[2*i] = count & 0x00ff;
			    payload[2*i+1] = (count & 0xff00) >> 8;
		    }
		    memset(encoded_payload, 0, 14);

		    // set mcs count
		    encoded_payload[0] = MCS;
		    if (GI)
			encoded_payload[0] |= HT_FLAG_GI;
		    if (BW)
			encoded_payload[0] |= HT_FLAG_40;

		    // set the location code
		    encoded_payload[1] = lcode & 0xff;

		    *encoded_counter = htonl(count);
		    *encoded_max = htonl(npackets);
		    *encoded_session = htonl(session_id);

		    metapack = lcpa_init();

		    // create timestamp
		    gettimeofday(&time, NULL);
		    timestamp = time.tv_sec * 1000000 + time.tv_usec;

		    lcpf_data(metapack,fcflags,duration,RA_MAC,TA_MAC,RA_MAC,TA_MAC,fragement,sequence);

		    lcpf_add_ie(metapack, 0, strlen("packet_injection"), "packet_injection");
		    lcpf_add_ie(metapack, 10, 14, encoded_payload);
		    lcpf_add_ie(metapack, 11, 2*PAYLOAD_LEN, payload);
		    lcpf_add_ie(metapack, 12, strlen((char *) payload_1), payload_1);

		    // convert the lorcon metapack to a lorcon packet for sending
		    txpack = (lorcon_packet_t *) lorcon_packet_from_lcpa(context, metapack);
		    lorcon_packet_set_mcs(txpack, 1, MCS, GI, BW);
		    if (lorcon_inject(context,txpack) < 0 )
			return -1;

		    usleep(interval);

		    fflush(stdout);
		    totalcount++;

		    lcpa_free(metapack);
		}
	    flag = 0;
    }
}
 
int main(int argc, char *argv[]) {
    pthread_t tid1, tid2;

    /* ---------------------------------- socket variable init---------------------------------- */   
    char   *hostname = NULL;
    int    port;
    int    ret;

    fd_set readfds,writefds,exceptfds;

    FD_ZERO(&readfds);
    FD_ZERO(&writefds);
    FD_ZERO(&exceptfds);

    u_int8_t    tmp_int8;
    u_int16_t   buf_len;

    unsigned int    src_addr;

    /* ---------------------------------- injector variable init---------------------------------- */

    char *interface = NULL;
    //unsigned int lcode = 0;
    unsigned int npackets = 100;

    int value[6];
    int c,i,tmp;
    int channel, ch_flags;

    lorcon_driver_t *drvlist, *driver;
    lorcon_t *context;

    lcpa_metapack_t *metapack;
    lorcon_packet_t *txpack;

    /* delay interval */
    unsigned int interval = 1;
    unsigned int ttime = 1;
    int BW = 0;
    int GI = 0; 

    uint8_t *dmac = "\x04\xF0\x21\x32\xBD\xA5";
    uint8_t *bmac = "\x00\xDE\xAD\xBE\xEF\x00";

    uint8_t RA_MAC[6];
    RA_MAC[0] = 0x04;
    RA_MAC[1] =0xF0;
    RA_MAC[2] =0x21;
    RA_MAC[3] =0x32;
    RA_MAC[4] =0xBD;
    RA_MAC[5] =0xA5;
    uint8_t *TA_MAC;
    uint8_t *DA_MAC = RA_MAC;
    uint8_t *BSSID_MAC = bmac;

    // Beacon Interval
    int beacon_interval = 100;

    // Capabilities
    int capabilities = 0x0421;

    // Session ID
    uint32_t session_id;
    FILE *urandom;

    /* ---------------------------------- UI ---------------------------------- */

    printf ("%s - packet injector NEW!\n", argv[0]);
    printf ("-----------------------------------------------------\n\n");
    while ((c = getopt(argc, argv, "hi:c:m:b:g:n:t:d:o:p:a:")) != EOF) {
	switch (c) {
	case 'i': 
		interface = strdup(optarg);
		break;
	case 'c':
		if (lorcon_parse_ht_channel(optarg, &channel, &ch_flags) == 0) {
	    		printf("ERROR: Unable to parse channel\n");
	    		return -1;
		}
		break;
	case 'm':
		if (sscanf(optarg, "%u", &MCS) != 1){
		    printf("ERROR: Unable to parse MCS idex\n");
		    return -1;
		}
		break;
    	case 'b':
		if (sscanf(optarg, "%u", &BW) != 1){
		    printf("ERROR: Unable to parse bandwidth \n");
		    return -1;
		}
		break;
	case 'g':
		if (sscanf(optarg, "%u", &GI) != 1){
		    printf("ERROR: Unable to parse guard interval \n");
		    return -1;
		}
		break;
	case 'n':
                if (sscanf(optarg, "%u", &npackets) != 1) {
                    printf("ERROR: Unable to parse number of packets\n");
                    return -1;
                }
                break;
	case 't':
                if (sscanf(optarg, "%u", &ttime) != 1){
                    printf("ERROR: Unable to parse transmission delay");
                    return -1;
                }
                break;
    	case 'd':
		if (sscanf(optarg, "%u", &interval) != 1) {
		    printf("ERROR: Unable to parse interpacket delay\n");
		    return -1;
		}
		break;
        case 'o':
		hostname = strdup(optarg);		
                break;
        case 'p':
                if (sscanf(optarg, "%u", &port) != 1) {
                    printf("ERROR: Unable to parse server port\n");
                    return -1;
                }
                break;
	case 'a':
		tmp = sscanf(optarg, "%x:%x:%x:%x:%x:%x", &value[0],&value[1],&value[2],&value[3],&value[4],&value[5]);
		printf("Read MAC, num:%d\n",tmp);
		if (6 == tmp ){
			printf("Read MAC, entering loop\n");
			for(i = 0; i < 6; i++){
				printf("Read MAC, loop index:%d\n",i);
				RA_MAC[i] = (uint8_t)value[i];	
			}
		}else{
		    printf("ERROR: Unable to parse MAC address\n");
		    return -1;
		}
		break;	
	case 'h':
		printf("ERROR: cannot parse the input\n");
		usage(argv);
		return -1;
		break;

	default:
		usage(argv);
		return -1;
		break;
	}
    }

    if ( interface == NULL) { 
	printf ("ERROR: Interface, or channel not set (see injector -h for more info)\n");
	return -1;
    }

    if ( hostname == NULL) {
        printf ("ERROR: hostname not set (see injector -h for more info)\n");
        return -1;
    }

    if ((urandom = fopen("/dev/urandom", "rb")) == NULL) {
        printf("ERROR:  Could not open urandom for session id: %s\n", strerror(errno));
        return -1;
    }

    /* ---------------------------------- client_main init---------------------------------- */
    fd = open_csi_device();
    if (fd < 0){
        perror("Failed to open the CSI device...");
        return 0;
    }

    memset(&pin,0,sizeof(pin));
    pin.sin_family = AF_INET;
    pin.sin_port   = htons(port);

    if ((hp = gethostbyname(hostname))!= NULL){
        pin.sin_addr.s_addr = ((struct in_addr *)hp->h_addr)->s_addr;
    }else{
        pin.sin_addr.s_addr = inet_addr(hostname);
    }

    // opening a socket and check whether it is successfully opened
    if((sock = (int)socket(AF_INET,SOCK_STREAM,0)) == -1){
        perror("socket");
        return 0;
    }
    printf("Waiting for the connection!\n");
    // connect to the server
    ret = connect(sock,(const struct sockaddr *)&pin,sizeof(pin));
    if(ret == -1){
        perror("connect");
        exit_program();
        return 0;
    }
    printf("Connection with server is built!\n");

    FD_SET(sock,&readfds);
    FD_SET(sock,&writefds);
    FD_SET(sock,&exceptfds);

    if (signal(SIGINT, sig_handler) == SIG_ERR){
        printf("Can't catch SIGINT\n");
        exit_program();
        return 0;
    }

    flag = 0;
    printf("sock: %d \n", sock);

    /* ---------------------------------- injector init---------------------------------- */
    fread(&session_id, 4, 1, urandom);
    fclose(urandom);

    printf("[+] Using interface %s\n",interface);

    if ((driver = lorcon_auto_driver(interface)) == NULL) {
        printf("[!] Could not determine the driver for %s\n", interface);
        return -1;
    } else {
        printf("[+]\t Driver: %s\n",driver->name);
    }

    if ((context = lorcon_create(interface, driver)) == NULL) {
        printf("[!]\t Failed to create context");
        return -1;
    }

    // Create Monitor Mode Interface
    if (lorcon_open_injmon(context) < 0) {
        printf("[!]\t Could not create Monitor Mode interface!\n");
        return -1;
    } else {
        printf("[+]\t Monitor Mode VAP: %s\n\n",lorcon_get_vap(context));
        lorcon_free_driver_list(driver);
    }

    // Get the MAC of the radio
    if (lorcon_get_hwmac(context, &TA_MAC) <= 0) {
        printf("[!]\t Could not get hw mac address\n");
        return -1;
    }

    printf("[+]\t Using MAC: %02x:%02x:%02x:%02x:%02x:%02x \n",TA_MAC[0],TA_MAC[1],TA_MAC[2],TA_MAC[3],TA_MAC[4],TA_MAC[5]);
    printf("[+]\t RX MAC: %02x:%02x:%02x:%02x:%02x:%02x \n",RA_MAC[0],RA_MAC[1],RA_MAC[2],RA_MAC[3],RA_MAC[4],RA_MAC[5]);
    // Set the channel we'll be injecting on
    lorcon_set_ht_channel(context, channel, ch_flags);

    printf("[+]\t Using channel: %d flags %d\n", channel, ch_flags);
    printf("\n[.]\tMCS %u %s %s\n\n", MCS, BW ? "40MHz" : "20MHz", GI ? "short-gi" : "long-gi");

    /*struct injector_args *args = calloc (sizeof (struct injector_args), 1);
    args->context = context;
    args->metapack = metapack;
    args->txpack = txpack;
    args->BW = BW;
    args->GI = GI;
    args->npackets = npackets;
    args->interval = interval;
    //memcpy(args->RA_MAC, RA_MAC);
    //args->TA_MAC = TA_MAC;
    args->session_id = session_id;
    args->ttime = ttime;
*/
    /* ---------------------------------- thread init---------------------------------- */
    int n1 = 1, n2 = 2, n3 = 3;

    if(pthread_create(&tid2, NULL, update_mcs, (void *)&n2)!=0)
	    printf("failed to create thread1 for msocket \n");
    else
	    printf("update_mcs thread successfully created \n");

    if(pthread_create(&tid1, NULL, estimate_csi, (void *)&n1)!=0)
	    printf("failed to create thread1 for msocket \n");
    else 
	    printf("estimate_csi thread successfully created \n");

//    if(pthread_create(&tid2, NULL, update_mcs, (void *)&n2)!=0)
//            printf("failed to create thread1 for msocket \n");
//    else
//	    printf("update_mcs thread successfully created \n");

//    if(pthread_create(&tid2, NULL, inject_data, (void *)args)!=0)
//	    printf("failed to create thread2 for injector \n");

//    pthread_join(tid2, NULL);
//    pthread_join(tid1, NULL);

//    while(1);

    printf("\n");
    // Close the interface
    lorcon_close(context);
    // Free the LORCON Context
    lorcon_free(context);	
//    exit_program();
//    free(csi_status);
//    free(args1);
    pthread_exit(NULL);    
    return 0;
}

