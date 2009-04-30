#include <malloc.h>
#include <stdio.h>

struct Environment {
    struct Value* stack;
};

struct VTable {
    void (*exec)(struct Value* self, struct Environment* env);
    struct Value (*clone)(struct Value* self);
    void (*free)(struct Value* self);
    void (*show)(struct Value* self, int ap);
};

struct Value {
    struct VTable* vtable;
    void* data;
};

struct Value stack_pop(struct Environment* env) {
    return *--env->stack;
}

void stack_push(struct Environment* env, struct Value val) {
    *env->stack++ = val;
}

// App
struct AppData {
    int refs;
    struct Value func;
    struct Value arg;
};

void exec_App(struct Value* self, struct Environment* env) {
    struct AppData* d = (struct AppData*)self->data;
    if (--d->refs > 0) {
        stack_push(env, d->arg.vtable->clone(&d->arg));
        stack_push(env, d->func.vtable->clone(&d->func));
    }
    else {
        stack_push(env, d->arg);
        stack_push(env, d->func);
        free(d);
    }
}

struct Value clone_App(struct Value* self) {
    struct AppData* d = (struct AppData*)self->data;
    d->refs++;
    return *self;
}

void free_App(struct Value* self) {
    struct AppData* d = (struct AppData*)self->data;
    if (--d->refs == 0) {
        d->func.vtable->free(&d->func);
        d->arg.vtable->free(&d->arg);
        free(d);
    }
}

void show_App(struct Value* self, int ap) {
    struct AppData* d = (struct AppData*)self->data;
    if (ap) {
        printf("(");
    }
    d->func.vtable->show(&d->func, 0);
    printf(" ");
    d->arg.vtable->show(&d->arg, 1);
    if (ap) {
        printf(")");
    }
}

struct VTable App_VTable = { exec_App, clone_App, free_App, show_App };

struct Value new_App(struct Value func, struct Value arg) {
    struct AppData* d = (struct AppData*)malloc(sizeof(struct AppData));
    d->refs = 1;
    d->func = func;
    d->arg = arg;
    struct Value v = { &App_VTable, d };
    return v;
}



// Primitives

struct Value clone_prim(struct Value* self) {
    return *self;
}

void free_prim(struct Value* self) { }

void exec_I(struct Value* self, struct Environment* env) { }

void show_I(struct Value* self, int ap) { printf("I"); }

void exec_K(struct Value* self, struct Environment* env) {
    struct Value x = stack_pop(env);
    struct Value y = stack_pop(env);
    y.vtable->free(&y);
    stack_push(env, y);
}

void show_K(struct Value* self, int ap) { printf("K"); }

void exec_S(struct Value* self, struct Environment* env) {
    struct Value x = stack_pop(env);
    struct Value y = stack_pop(env);
    struct Value z = stack_pop(env);
    struct Value z2 = z.vtable->clone(&z);
    stack_push(env, new_App(y,z));
    stack_push(env, z2);
    stack_push(env, x);
}

void show_S(struct Value* self, int ap) { printf("S"); }

struct VTable I_VTable = { exec_I, clone_prim, free_prim, show_I };
struct VTable K_VTable = { exec_K, clone_prim, free_prim, show_K };
struct VTable S_VTable = { exec_S, clone_prim, free_prim, show_S };

struct Value I = { &I_VTable, NULL };
struct Value K = { &K_VTable, NULL };
struct Value S = { &S_VTable, NULL };


void interpret(struct Value v) {
    struct Value* stack_top = (struct Value*)malloc(sizeof(struct Value)*1024);
    struct Environment env = { stack_top };
    struct Value* cptr;
    stack_push(&env, v);

    while (env.stack > stack_top) {
        struct Value f = stack_pop(&env);
        f.vtable->show(&f, 0);
        printf(" | ");
        for (cptr = env.stack-1 ; cptr >= stack_top ; cptr--) {
            cptr->vtable->show(cptr, 1);
            printf(" ");
        }
        printf("\n");
        f.vtable->exec(&f, &env);
    }
}

int main() {
    struct Value x = new_App(new_App(new_App(S, I), I),
                             new_App(new_App(S, I), I));
    interpret(x);
}
