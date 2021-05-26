#define NULL ((void *) 0)
#define RED 1
#define BLACK 0

extern void *mallocN (int n);

struct tree {
    int color;
    int key;
    unsigned int value;
    struct tree *left, *right, *par;
};

typedef struct tree ** treebox;

int get_color1 (struct tree *p) {
    if (p == NULL) {
        return -1;
    } else {
        return p->color;
    }
}

int get_color2 (struct tree *p) {
    if (p == NULL) {
        return -1;
    } else {
        return p->color;
    }
}

void make_black (treebox root) {
    if (root == NULL) {
        return ;
    } else {
        struct tree * p = *root;
        if (p == NULL) {
            return;
        } else {
            p->color = BLACK;
        }
    }
}

struct tree * left_rotate (struct tree * l) {
    struct tree * r = l->right;
    struct tree * mid = r->left;
    l->right = mid;
    r->left = l;
    r->par = l->par;
    l->par = r;
    if (mid != NULL) {
        mid->par = l;
    }
    return r;
}

void left_rotate_wrap (struct tree * l, treebox root) {
    if (l->par == NULL) {
        *root = left_rotate(l);
    } else {
        struct tree * l_par = l->par;
        if (l_par->left == l) {
            l_par->left = left_rotate(l);
        } else {
            l_par->right = left_rotate(l);
        }
    }
}

struct tree * right_rotate (struct tree * r) {
    struct tree * l = r->left;
    struct tree * mid = l->right;
    r->left = mid;
    l->right = r;
    l->par = r->par;
    r->par = l;
    if (mid != NULL) {
        mid->par = r;
    }
    return l;
}

void right_rotate_wrap (struct tree * r, treebox root) {
    if (r->par == NULL) {
        *root = right_rotate(r);
    } else {
        struct tree * r_par = r->par;
        if (r_par->left == r) {
            r_par->left = right_rotate(r);
        } else {
            r_par->right = right_rotate(r);
        }
    }
}

void insert_balance (treebox t, treebox root) {
    struct tree * p = *t;
    struct tree * p_par, * p_gpar;
    for (; ; ) {
        p_par = p->par;
        if (get_color1(p_par) != RED) {
            return ;
        } else {
            p_gpar = p_par->par;
            if (p_gpar == NULL) {
                return ;
            } else {
                if (p_par == p_gpar->left) {
                    if (get_color2(p_gpar->right) == RED) {
                        p_par->color = BLACK;
                        p_gpar->right->color = BLACK;
                        p_gpar->color = RED;
                        p = p_gpar;
                    } else {
                        p_gpar->color = RED;
                        if (p == p_par->right) {
                            p->color = BLACK;
                            p_gpar->left = left_rotate(p_par);
                            right_rotate_wrap(p_gpar, root);
			    return;
                        } else {
                            p_par->color = BLACK;
                            right_rotate_wrap(p_gpar, root);
			    return; // added for convenient verification
                        }
                    }
                } else {
                    if (get_color2(p_gpar->left) == RED) {
                        p_par->color = BLACK;
                        p_gpar->left->color = BLACK;
                        p_gpar->color = RED;
                        p = p_gpar;
                    } else {
                        p_gpar->color = RED;
                        if (p == p_par->left) {
                            p->color = BLACK;
                            p_gpar->right = right_rotate(p_par);
                            left_rotate_wrap(p_gpar, root);
			    return;
                        } else {
                            p_par->color = BLACK;
                            left_rotate_wrap(p_gpar, root);
			    return; // added for convenient verification
                        }
                    }
                }
            }
        }
    }
}

void insert (treebox t, int x, unsigned int value) {
    treebox root = t;
    struct tree * p;
    struct tree * last_node = NULL;
    for (; ; ) {
        p = *t;
        if (p == NULL) {
            p = (struct tree *) mallocN (sizeof *p);
            p->color = RED;
            p->key = x;                 
            p->value = value; 
            p->left = NULL; 
            p->right = NULL;
            p->par = last_node;
            *t = p;
            break;
        } else {
            int y = p->key;
            if (x == y) {
                p->value = value;
                break;
            } else {
                last_node = p;
                if (x < y) {
                    t = &(p->left); 
                } else {
                    t = &(p->right);
                }
            }
        }
    }
    if (p->color == RED) {
        insert_balance(t, root);
    }
    make_black(root);
}
