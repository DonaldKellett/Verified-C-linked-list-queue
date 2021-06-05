#include <stddef.h>

extern void *malloc(size_t);
extern void free(void *);
extern void exit(int);

struct node {
  int value;
  struct node *next;
};

struct queue {
  struct node *front;
  struct node *back;
};

void queue_init(struct queue *q) { q->front = q->back = NULL; }

int queue_is_empty(struct queue *q) { return !q->front; }

int queue_front(struct queue *q) { return q->front->value; }

void queue_enqueue(struct queue *q, int value) {
  struct node *t;
  t = (struct node *)malloc(sizeof(struct node));
  if (!t)
    exit(1);
  t->value = value;
  t->next = NULL;
  if (!q->back)
    q->front = q->back = t;
  else
    q->back = q->back->next = t;
}

int queue_dequeue(struct queue *q) {
  int value;
  struct node *t;
  value = q->front->value;
  if (q->front == q->back) {
    free(q->front);
    q->front = q->back = NULL;
    return value;
  }
  t = q->front->next;
  free(q->front);
  q->front = t;
  return value;
}

int main(void) { return 0; }
