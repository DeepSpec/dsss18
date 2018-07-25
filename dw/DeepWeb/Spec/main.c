/*
  This program implements a swap server that accepts connections from multiple 
  clients. On each connection, the server receives bytes from the corresponding
  client until the buffer is full, at which point the received bytes are deemed 
  a "message". The server replies to this client with the last obtained 
  message, which could have been obtained from another client (on another 
  connection). This last obtained message is initially set to all zeroes.

  All these actions (accepting a new connection, receiving a message, and 
  sending a message) are interleaved.
 */

/*! Section ExternalTest */

#include "macros.h"
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <netinet/in.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <stdio.h>

#ifndef BUFFER_SIZE
#define BUFFER_SIZE 1024
#endif
#define INVALID_SOCKET -1

#ifdef DEBUG
#include <errno.h>
#include <stdarg.h>
static FILE *debug_file = NULL;
void START_LOG() {
  debug_file = fopen("/tmp/server_log", "a");
  if (NULL == debug_file) {
    perror("Could not open server log");
    exit(1);
  }
}
void PRINT(const char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  vfprintf(debug_file, fmt, args);
  va_end(args);
  fflush(debug_file);
}
void PERROR(const char *msg) {
  PRINT("%s: %s", msg, strerror(errno));
  perror(msg);
}
#endif

typedef int socket_fd;

typedef enum state {
  RECVING,
  SENDING,
  DONE,
  DELETED,
} state;

typedef struct connection {
  socket_fd fd;
  uint32_t request_len;
  uint8_t request_buffer[BUFFER_SIZE];
  uint32_t response_len;
  uint8_t response_buffer[BUFFER_SIZE];
  uint32_t num_bytes_sent;
  enum state st;
  struct connection* next;  
#ifdef DEBUG
  int connection_id;
#endif
} connection;

typedef struct store {
  uint32_t stored_msg_len;
  uint8_t stored_msg[BUFFER_SIZE];
} store;

void fd_zero_macro(fd_set* set) {
  FD_ZERO(set);
}

int fd_isset_macro(int fd, fd_set* set) {
  return FD_ISSET(fd, set);
}

void fd_set_macro(int fd, fd_set* set) {
  FD_SET(fd, set);
}

static int check_if_complete(uint8_t* buffer_ptr, uint32_t len) {
  if (BUFFER_SIZE == len) {
    return 1;
  }

  return 0;    
}

static connection* new_connection() {
  connection* result = (connection* )malloc(sizeof(connection));
  if(result == NULL) {
    return result;
  }
  result->fd = 0;
  result->request_len = 0;
  result->response_len = 0;
  result->num_bytes_sent = 0;
  result->st = RECVING;
  result->next = NULL;
#ifdef DEBUG
  static int next_cid = 0;
  result->connection_id = next_cid++;
#endif
  return result;
}

static store* new_store() {
  store* result = (store* )malloc(sizeof(store));
  if(result == NULL) {
    return result;
  }
  result->stored_msg_len = 0;
  uint8_t* buffer = result->stored_msg;
  memset(buffer, 0, BUFFER_SIZE);
  return result;
}


/*
  [populate_response] performs the swap: it populates the response buffer in
  [conn] with the last stored message, and updates the last stored message 
  to be the message received on this connection (stored in its request buffer).
 */
static int
populate_response(connection* conn, store* last_msg_store) {

  uint8_t* last_msg = last_msg_store->stored_msg;
  uint32_t last_msg_len = last_msg_store->stored_msg_len;
  
  // populate response
  conn->num_bytes_sent = 0;
  conn->response_len = last_msg_len;
  uint8_t* response_buffer = conn->response_buffer;

  memcpy(response_buffer, last_msg, last_msg_len);

  // now save the request
  uint32_t request_len = conn->request_len;
  last_msg_store->stored_msg_len = request_len;
  
  uint8_t* request_buffer = conn->request_buffer;
  memcpy(last_msg, request_buffer, /*!*/ request_len /*! request_len - 1 */);
  return 1;
}

static int
conn_read(connection* conn, store* last_msg_store) {
  int r;
  
  socket_fd conn_fd = conn->fd;
  uint32_t request_len = conn->request_len;
  uint8_t* request_buffer = conn->request_buffer;
  
  uint8_t* ptr = request_buffer + request_len;
  r = recv(conn_fd, ptr, BUFFER_SIZE - request_len, 0);
  uint32_t new_len; 

  if (r < 0) {
    return 0;
  }

  if (r == 0) {
#ifdef DEBUG
    PRINT("conn_read(%d): DELETED\n", conn->connection_id);
#endif

    conn->st = DELETED; // mark for cleanup later
    return 0;
  }

#ifdef DEBUG
  PRINT("conn_read(%d): Received %d bytes\n", conn->connection_id, r);
#endif
  
  new_len = request_len + r;
  conn->request_len = new_len;

  int complete = check_if_complete(request_buffer, new_len);
  if (complete == 0) {
    return 0;
  }

  int response_ok = 0;
  response_ok = populate_response(conn, last_msg_store);
  if (response_ok == 0) {
    // fatal error
    conn->st = DELETED;
    return 0;
  }

#ifdef DEBUG
  PRINT("conn_read: Transiting to SENDING\n");
#endif

  conn->st = SENDING;
  return 0;
}

static void reset_connection(connection* conn, socket_fd fd) {

  uint8_t* request = conn->request_buffer;
  uint8_t* response = conn->response_buffer;

  conn->fd = fd;
  conn->st = RECVING;
  conn->response_len = 0;
  conn->num_bytes_sent = 0;
  conn->request_len = 0;
  memset(request, 0, BUFFER_SIZE);
  memset(response, 0, BUFFER_SIZE);  
} 

static int conn_write(connection* conn) {
  int r;
  
  socket_fd conn_fd = conn->fd;
  uint32_t response_len = conn->response_len;
  uint32_t num_bytes_sent = conn->num_bytes_sent;
  uint8_t* response = conn->response_buffer + num_bytes_sent;
  uint32_t num_bytes_to_send = response_len - num_bytes_sent;
  
  r = send(conn_fd, response, num_bytes_to_send, 0);

#ifdef DEBUG
  PRINT("conn_write(%d): Sent %d bytes\n", conn->connection_id, num_bytes_to_send);
#endif

  if(r < 0) {
    conn->st = DELETED; // client possibly disconnected
    return 0;
  }

  conn->num_bytes_sent = num_bytes_sent + r;

  if(r < num_bytes_to_send) {
    return 0;
  }

  // reset
  reset_connection(conn, conn_fd);

  return 0;
}

static int
process(connection* conn, store* last_msg_store) {

  int r;
  state conn_st = conn->st;
  if(conn_st == RECVING) {
    return conn_read(conn, last_msg_store);
  }
  if(conn_st == SENDING) {
    return conn_write(conn);
  }

  return 0;
}


/* [accept_connection] accepts a new connection on the socket, creates a 
   connection structure for it, and links it into the head of the linked list.
 */
static int accept_connection(socket_fd socket,
                             connection** head) {
  socket_fd fd;
  connection* conn;

  fd = accept(socket, NULL, NULL);
  if (fd < 0) {
    return -1;
  }

  if (fd >= FD_SETSIZE) {
    shutdown(fd, SHUT_RDWR);
    close(fd);
    return -1;
  }

  conn = new_connection();
  if (conn == NULL) {
    shutdown(fd, SHUT_RDWR);
    close(fd);
    return -1;
  }

#ifdef DEBUG
  PRINT("accept -> %d\n", conn->connection_id);
#endif

  reset_connection(conn, fd);

  connection* old_head = *head;
  conn->next = old_head;
  *head = conn;

  return 0;
}

static int add_to_fd_set(socket_fd fd,
		  fd_set* set,
		  socket_fd* max_fd) {
  
  if (set == NULL) {
    return -1;
  }

  if (fd >= FD_SETSIZE) {
    return -1;
  }
  if (fd < 0) {
    return -1;
  }

  if (max_fd == NULL) {
    return -1;
  }
  if (fd == INVALID_SOCKET) {
    return -1;
  }

  fd_set_macro(fd, set);

  int tmp = *max_fd;
  if(fd > tmp) {
    *max_fd = fd;
  }

  return 0;
}

static void
monitor_connections(connection* head, fd_set* rs, fd_set* ws,
		    socket_fd* max_fd) {

  connection* curr = head;
  state curr_st;
  socket_fd curr_fd;
  
  while (curr != NULL) {
    curr_st = curr->st;
    curr_fd = curr->fd;

    if (curr_st == RECVING) {
      add_to_fd_set(curr_fd, rs, max_fd);
    }

    if (curr_st == SENDING) {
      add_to_fd_set(curr_fd, ws, max_fd);
    }
    curr = curr->next;
  }
  
}

static void 
process_connections(connection *head, fd_set* rs, fd_set* ws,
		    store* last_msg_store) {

  int socket_ready;
  connection* curr = head;
  state curr_st;
  socket_fd curr_fd;


  /*
    This loop iterates over all [connections] in the list pointed to by [head]
    and does a [process] step.
    
    EX prefix : list (connection * sockfd * val),
    EX suffix : list (connection * sockfd * val),
    EX st : SocketMap,
    EX last_msg : string,
    EX curr_ptr : val, such that

    (1) Memory is laid out as: 
    - SOCKAPI st ;
      FD_SET Tsh read_set read_set_ptr;
      FD_SET Tsh write_set write_set_ptr;
      
      TRACE ( (select_loop
                 server_addr
                 BUFFER_SIZE
                 (true, (map proj_conn (prefix ++ suffix), last_msg)))
                ;; k );

      lseg LS Tsh Tsh (map rep_full_conn prefix) head_ptr curr_ptr;
      lseg LS Tsh Tsh (map rep_full_conn suffix) curr_ptr nullval;
      field_at Tsh (Tstruct _store noattr) [] (rep_store last_msg)
               msg_store_ptr

    (2) The following properties all hold:
    - consistent_world st
    - lookup_socket st server_fd = ListeningSocket server_addr
    - Forall (fun '(conn, fd, ptr) =>
        consistent_state BUFFER_SIZE st (conn, fd)) prefix;
    - Forall (fun '(conn, fd, ptr) =>
        consistent_state BUFFER_SIZE st (conn, fd)) suffix;
    - exists old_prefix,
      - connections = old_prefix ++ suffix
      - map proj_fd old_prefix = map proj_fd prefix, i.e. fds are never changed
      - map conn_id
          (map proj_conn old_prefix) = map conn_id (map proj_conn prefix),
	i.e. ids are never changed
      - map proj_ptr old_prefix = map proj_ptr prefix, i.e. pointers are never
        changed.
    - NoDup
        (map conn_id
	  (map proj_conn
	    (filter
	      (fun c => (has_conn_state RECVING c
	        || has_conn_state SENDING c)%bool)
		(prefix ++ suffix)))), i.e. connection ids among 
      RECVING/SENDING connections are distinct. 
    
   */
  while (curr != NULL) {
    curr_fd = curr->fd;
    int read_socket_ready = fd_isset_macro(curr_fd, rs);
    int write_socket_ready = fd_isset_macro(curr_fd, ws);
    socket_ready = 0;
    if (read_socket_ready) {
      socket_ready = 1;
    }
    else if (write_socket_ready) {
      socket_ready = 1;
    }
    
    if (socket_ready > 0) {
      process(curr, last_msg_store);
    }
    curr = curr->next;
  }
    
}


int select_loop(socket_fd server_socket, store* last_msg_store) {
  fd_set rs, ws, es;
  struct timeval timeout;
  
  connection *head = NULL;
  socket_fd maxsock = INVALID_SOCKET;
  
  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  head = NULL;

  /*
    In this loop, [head] is a pointer to a linked list of connection 
    structures. In each iteration, a new connection is accepted if one is 
    pending on the server socket, and work is performed for each connection 
    in the linked list depending on its state. 

    EX connections: list (connection * sockfd * val),
    EX last_msg : string,                  
    EX st : SocketMap,
    EX read_set : FD_Set,
    EX write_set : FD_Set,
    EX exception_set : FD_Set,
    EX head_ptr : val, such that

    (1) Memory is laid out as: 
    - SOCKAPI st ;
      FD_SET Tsh read_set v_rs;
      FD_SET Tsh write_set v_ws;
      FD_SET Tsh exception_set v_es;
      ...
      field_at Tsh (tptr (Tstruct _connection noattr)) [] head_ptr v_head;
      lseg LS Tsh Tsh
        (map rep_full_conn connections)
        head_ptr nullval;
      ... 
      TRACE (r <- select_loop server_addr BUFFER_SIZE
                    (true, (map proj_conn connections, last_msg))
		    ;; k);
      field_at Tsh (Tstruct _store noattr) [] (rep_store last_msg) msg_store_ptr

    (2) The following properties hold:
    - consistent_world st, i.e. all connected sockets are associated with 
      distinct connection IDs;
    - lookup_socket st server_fd = ListeningSocket server_addr
    - Forall (fun '(conn, fd, ptr) => consistent_state BUFFER_SIZE st (conn, fd))
        connections, i.e. all connections in the list are "consistent"
    - NoDup (map descriptor (map proj_fd connections)), i.e. all file 
      descriptors in the list are distinct. 
    - NoDup (map conn_id
              (map proj_conn
	        (filter
		  (fun c => (has_conn_state RECVING c)
		    || (has_conn_state SENDING c))%bool
		    connections))), 
      i.e. connection IDs associated with RECVING/SENDING connection structures 
      are distinct.  
   */

  while (1 == 1) {
    fd_zero_macro(&rs);
    fd_zero_macro(&ws);
    fd_zero_macro(&es);

    maxsock = INVALID_SOCKET;

    add_to_fd_set(server_socket, &rs, &maxsock);

    connection* tmp_head = head;

    // loop through all connections in the list to add file descriptors
    // to the fdsets
    monitor_connections(tmp_head, &rs, &ws, &maxsock);

    int tmp = maxsock;
    
    int num_ready = select(tmp + 1, &rs, &ws, &es, &timeout);
    if (num_ready <= 0) {
      continue;
    }

    int socket_ready = fd_isset_macro(server_socket, &rs);
    
    if (socket_ready) {
      accept_connection(server_socket, &head);
#ifdef DEBUG
      PRINT("select_loop: New connection accepted\n");
#endif
    }

    tmp_head = head;

    // loop through all connections in the list to perform work if needed
    process_connections(tmp_head, &rs, &ws, last_msg_store);
    
  }
  
  return 0;
}

static void zeroize_addr(struct sockaddr_in* addr) {
  memset(addr, 0, sizeof(struct sockaddr_in));
}

static int bind_socket(socket_fd fd, int port) {

  struct sockaddr_in addr;
  zeroize_addr(&addr);

  int addr_len = sizeof(struct sockaddr_in);
  addr.sin_family = AF_INET;
  addr.sin_port = htons(port);

  int r = bind(fd, (struct sockaddr* )&addr, addr_len);
  if(r < 0) {
    return -1;
  }

  return 0;
}

static void init_store (store* last_msg_store) {
  last_msg_store->stored_msg_len = BUFFER_SIZE;
  char* last_msg = (char* )last_msg_store->stored_msg;
  memset(last_msg, /*!*/ '0' /*! 'X' */, BUFFER_SIZE); 
  // memset(last_msg, '0', BUFFER_SIZE);
}

int main() {

#if DEBUG
  START_LOG();
  PRINT("main: New server\n");
#endif

  socket_fd fd;
  int r;

  store* last_msg_store = new_store();
  if(last_msg_store == NULL) {
    exit(0);
  }

  init_store(last_msg_store);
  
  fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
#if DEBUG
    PERROR("socket() failed");
#endif
    exit(0);
  }

  if (fd >= FD_SETSIZE) {
    exit(0);
  }

  int port = 8000;
  r = bind_socket(fd, port);
  if (r < 0) {
#if DEBUG
    PERROR("bind() failed");
#endif
    exit(0);
  } 

  r = listen(fd, SOMAXCONN);
  if (r < 0) {
#if DEBUG
    PERROR("listen() failed");
#endif
    exit(0);
  }

#if DEBUG
  PRINT("main: Entering loop...\n");
#endif
  select_loop(fd, last_msg_store);
}
