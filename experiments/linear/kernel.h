#include <sys/mman.h>
#include <stdio.h>

#define I -1
#define B -2
#define C -3
#define PAIR -4
#define FST -5
#define SND -6

struct Head {
    int tag;
    int args;
    struct Link* head;
    struct Link* tail;
};

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
        f->tail = free;
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

struct Pool make_pool(size_t size) {
    void* arena = mmap(0, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (arena == (void*)(-1)) {
        perror("make_pool");
    }
    int items = size / sizeof(union PoolItem);
    int i;
    union PoolItem* cptr = (union PoolItem*)arena;
    struct Pool ret;
    for (i = 0; i < items; i++) {
        cptr->next = cptr+1;
        cptr++;
    }
    (cptr-1)->next = 0;
    ret.head = (union PoolItem*)arena;
    return ret;
}

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

void recursive_free(struct Pool* pool, struct Head* node) {
    struct Link* cptr = node->head;
    while (cptr) {
        recursive_free(pool, cptr->link);
        struct Link* next = cptr->next;
        free_item(pool, cptr);
        cptr = next;
    }
    free_item(pool, node);
}

struct Head* append(struct Pool* pool, int arity, struct Head* f, struct Head* pfx, struct Link* link) {
    if (pfx->args == 0) {
        pfx->head = pfx->tail = link;
        pfx->args = f->args - arity;
    }
    else {
        pfx->tail->next = link;
        pfx->tail = f->tail;
        pfx->args += f->args - arity;
    }
    free_item(pool, f);
    return pfx;
}


typedef struct Head* (*defnptr_t)(struct Pool* pool);
extern defnptr_t DEFNS[];


struct Head* reduce(struct Pool* pool, struct Head* f) {
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
                f = append(pool, 3, f, apply(x,apply(y,z,ly),lx), lz->next);
                free_item(pool, lz);
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
                f = append(pool, 3, f, apply(apply(x,z,lx), y, ly), lz->next);
                free_item(pool, lz);
                goto AGAIN;
            }
            break;
        case I:  /* Ix = x */
            if (f->args >= 1) {
                struct Link* lx = f->head;
                struct Head* x = lx->link;
                f = append(pool, 1, f, x, lx->next);
                free_item(pool, lx);
                goto AGAIN;
            }
            break;
        case PAIR: break;
        case FST:  /* FST (PAIR f g x) = f x */
            if (f->args >= 1) {
                struct Link* lp = f->head;
                struct Head* p = reduce(pool, lp->link);
                if (p->tag == PAIR) {
                    struct Link* ffp = lp->next;
                    struct Head* ff = ffp->link;
                    struct Link* gfp = ffp->next;
                    struct Head* gf = gfp->link;
                    struct Link* xp = gfp->next;
                    struct Head* x = xp->link;
                    f = append(pool, 1, f, apply(ff, x, ffp), lp->next);
                    recursive_free(pool, gf);
                    free_item(pool, lp);
                    free_item(pool, gfp);
                    free_item(pool, xp);
                    goto AGAIN;
                }
            }
            break;
        case SND:  /* SND (PAIR f g x) = g x */
            if (f->args >= 1) {
                struct Link* lp = f->head;
                struct Head* p = reduce(pool, lp->link);
                if (p->tag == PAIR) {
                    struct Link* ffp = lp->next;
                    struct Head* ff = ffp->link;
                    struct Link* gfp = ffp->next;
                    struct Head* gf = gfp->link;
                    struct Link* xp = gfp->next;
                    struct Head* x = xp->link;
                    f = append(pool, 1, f, apply(gf, x, gfp), lp->next);
                    recursive_free(pool, ff);
                    free_item(pool, lp);
                    free_item(pool, ffp);
                    free_item(pool, xp);
                    goto AGAIN;
                }
            }
            break;
        default: {
            struct Head* h = DEFNS[f->tag](pool);
            if (h->args > 0) {
                h->tail->next = f->head;
            }
            else {
                h->head = h->tail = f->head;
            }
            h->args += f->args;
            free_item(pool, f);
            f = h;
            goto AGAIN;
            break;
        }
    }
    return f;
}

void print_head(struct Head* h) {
    switch (h->tag) {
        case B: printf("B"); break;
        case C: printf("C"); break;
        case I: printf("I"); break;
        default: printf("[%d]", h->tag); break;
    }

    struct Link* cptr = h->head;
    while (cptr) {
        if (cptr->link->args > 0) {
            printf("(");
            print_head(cptr->link);
            printf(")");
        }
        else {
            print_head(cptr->link);
        }
        cptr = cptr->next;
    }
}

int main() {
    struct Pool pool = make_pool(1024*1024*16); /* 16 MB */
    struct Head head = { 0, 0, 0, 0 };
    struct Head* ret = reduce(&pool, &head);
    print_head(ret);
    printf("\n");
}
