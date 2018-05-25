#include <stddef.h>

struct list {int head; struct list *tail;};

unsigned sumlist (struct list *p) {
  unsigned s = 0;
  struct list *t = p;
  unsigned h;
  while (t) {
     h = t->head;
     t = t->tail;
     s = s + h;
  }
  return s;
}

struct list *append (struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    u = t->tail;
    while (u!=NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

