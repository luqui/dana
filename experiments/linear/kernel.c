struct Head {
    int tag;
    int args;
    struct Link* head;
    struct Link* tail;
};

#define I -1
#define B -2
#define C -3

struct Link {
    struct Link* next;
    struct Head* link;
};

struct Head* apply(struct Head* f, struct Head* x, struct Link* free) {
    free->link = x;
    free->next = 0;
    if (f->args == 0) {
        f->args = 1;
        f->head = f->tail = free;
    }
    else {
        f->args++;
        f->tail->next = free;
    }
    return f;
}

union PoolItem {
    union PoolItem* next;
    struct Head head;
    struct Link link;
};

struct Pool {
    union PoolItem* head;
};

struct Head* alloc_Head(struct Pool* pool) {
    struct Head* ret = &pool->head->head;
    pool->head = pool->head->next;
    return ret;
};

struct Link* alloc_Link(struct Pool* pool) {
    struct Link* ret = &pool->head->link;
    pool->head = pool->head->next;
    return ret;
}

void free_item(struct Pool* pool, void* node) {
    union PoolItem* item = (union PoolItem*)node;
    item->next = pool->head;
    pool->head = item;
}

typedef struct Head* (*defnptr_t)(struct Pool* pool);
extern defnptr_t DEFNS[];


struct Node* reduce(struct Pool* pool, struct Head* f) {
AGAIN:
    switch (f->tag) {
        case B:  /* Bxyz = x(yz) */
            if (f->args >= 3) {
                struct Link* lx = f->head;
                struct Head* x = lx->link;
                struct Link* ly = lx->next;
                struct Head* y = ly->link;
                struct Link* lz = ly->next;
                struct Head* z = lz->link;
                free_item(pool, lz);
                f = apply(x,apply(y,z,ly),lx);
                goto AGAIN;
            }
            break;
        case C:  /* Cxyz = xzy */
            if (f->args >= 3) {
                struct Link* lx = f->head;
                struct Head* x = lx->link;
                struct Link* ly = lx->next;
                struct Head* y = ly->link;
                struct Link* lz = ly->next;
                struct Head* z = lz->link;
                free_item(pool, lz);
                f = apply(apply(x,z,lx), y, ly);
                goto AGAIN;
            }
        case I:  /* Ix = x */
            if (f->args >= 1) {
                struct Link* lx = f->head;
                struct Head* x = lx->link;
                free_item(pool, lx);
                f = x;
                goto AGAIN;
            }
            break;
        default:
            f = DEFNS[f->tag](pool);
            goto AGAIN;
    }
}
