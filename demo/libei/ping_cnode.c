#include <ei.h>

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#ifndef MAXATOMLEN_UTF8
#define MAXATOMLEN_UTF8 MAXATOMLEN
#endif

struct options {
  const char *alive;
  const char *server;
  const char *cookie;
};

static void usage(const char *argv0) {
  fprintf(stderr,
          "usage: %s [--alive NAME] [--server NAME] [--cookie COOKIE]\n",
          argv0);
}

static int parse_args(int argc, char **argv, struct options *opts) {
  int i;

  opts->alive = "filc_libei_ping";
  opts->server = "ping_server";
  opts->cookie = "filc_libei_cookie";

  for (i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--alive") == 0 && i + 1 < argc) {
      opts->alive = argv[++i];
    } else if (strcmp(argv[i], "--server") == 0 && i + 1 < argc) {
      opts->server = argv[++i];
    } else if (strcmp(argv[i], "--cookie") == 0 && i + 1 < argc) {
      opts->cookie = argv[++i];
    } else {
      usage(argv[0]);
      return -1;
    }
  }

  return 0;
}

static int send_pong(int fd, erlang_pid *pid, const char *node_name) {
  ei_x_buff xb;
  int rc;

  if (ei_x_new_with_version(&xb) != 0) {
    fprintf(stderr, "failed to allocate ei_x_buff\n");
    return -1;
  }

  ei_x_encode_tuple_header(&xb, 2);
  ei_x_encode_atom(&xb, "pong");
  ei_x_encode_string(&xb, node_name);

  rc = ei_send(fd, pid, xb.buff, xb.index);
  ei_x_free(&xb);

  if (rc != 0) {
    fprintf(stderr, "ei_send failed\n");
    return -1;
  }

  return 0;
}

int main(int argc, char **argv) {
  struct options opts;
  ei_cnode ec;
  ErlConnect con;
  erlang_msg msg;
  ei_x_buff x;
  int port;
  int lfd;
  int fd;
  int r;

  if (parse_args(argc, argv, &opts) != 0) {
    return 2;
  }

  if (ei_init() != 0) {
    fprintf(stderr, "ei_init failed\n");
    return 1;
  }

  if (ei_connect_init(&ec, opts.alive, opts.cookie, 0) < 0) {
    fprintf(stderr, "ei_connect_init failed for alive=%s\n", opts.alive);
    return 1;
  }

  port = 0;
  lfd = ei_listen(&ec, &port, 5);
  if (lfd < 0) {
    fprintf(stderr, "ei_listen failed\n");
    return 1;
  }

  if (ei_publish(&ec, port) < 0) {
    fprintf(stderr, "ei_publish failed (is epmd running?)\n");
    close(lfd);
    return 1;
  }

  fprintf(stderr, "READY node=%s server=%s port=%d\n", ei_thisnodename(&ec), opts.server, port);

  fd = ei_accept(&ec, lfd, &con);
  if (fd < 0) {
    fprintf(stderr, "ei_accept failed\n");
    close(lfd);
    return 1;
  }

  fprintf(stderr, "ACCEPT from=%s\n", con.nodename);

  if (ei_x_new(&x) != 0) {
    fprintf(stderr, "ei_x_new failed\n");
    close(fd);
    close(lfd);
    return 1;
  }

  for (;;) {
    int idx;
    int version;
    int arity;
    char atom[MAXATOMLEN_UTF8];
    erlang_pid from;

    r = ei_xreceive_msg_tmo(fd, &msg, &x, 5000);
    if (r == ERL_TICK) {
      continue;
    }

    if (r == ERL_ERROR) {
      fprintf(stderr, "ei_xreceive_msg_tmo failed errno=%d (%s)\n", errno, strerror(errno));
      ei_x_free(&x);
      close(fd);
      close(lfd);
      return 1;
    }

    if (r != ERL_MSG) {
      continue;
    }

    if (msg.msgtype != ERL_REG_SEND || strcmp(msg.toname, opts.server) != 0) {
      continue;
    }

    idx = 0;
    version = 0;
    arity = 0;
    memset(atom, 0, sizeof(atom));

    if (ei_decode_version(x.buff, &idx, &version) != 0) {
      fprintf(stderr, "failed to decode version\n");
      continue;
    }

    if (ei_decode_tuple_header(x.buff, &idx, &arity) != 0 || arity != 2) {
      fprintf(stderr, "expected {ping, Pid}\n");
      continue;
    }

    if (ei_decode_atom(x.buff, &idx, atom) != 0 || strcmp(atom, "ping") != 0) {
      fprintf(stderr, "expected ping atom\n");
      continue;
    }

    if (ei_decode_pid(x.buff, &idx, &from) != 0) {
      fprintf(stderr, "failed to decode pid\n");
      continue;
    }

    if (send_pong(fd, &from, ei_thisnodename(&ec)) != 0) {
      ei_x_free(&x);
      close(fd);
      close(lfd);
      return 1;
    }

    fprintf(stderr, "PONG sent to Erlang pid\n");
    break;
  }

  ei_x_free(&x);
  close(fd);
  close(lfd);
  return 0;
}
