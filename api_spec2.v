Require Import VST.floyd.proofauto.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Export RBTree.definitions2.
Require Import RBTree.AuxiliaryTac.
Require Import Coq.Logic.Classical.
Import ListNotations.
Local Open Scope Z.

(* --------------------------------------------------------- *)


(* --------------------------------------------------------- *)
Module getColor1.

Definition get_color1_spec :=
  DECLARE _get_color1
  WITH p: val,
       p_par: val,
       p_l: val,
       p_r: val,
       n: Node,
       b: bool
  PRE [tptr t_struct_tree]
    PROP (b = false <-> p = nullval)
    PARAMS (p)
    GLOBALS ()
    SEP (if b then
           data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node n))),
                                      (Vint (Int.repr (key_of_node n)),
                                       (Vint (Int.repr (value_of_node n)),
                                        (p_l, (p_r, p_par))))) p
         else emp)
  POST [tint]
    PROP (b = false <-> p = nullval)
    RETURN ( Vint (Int.repr (
      if b then (* p <> nullval *)
        Col2Z (color_of_node n)
      else -1)) )
    SEP (if b then
           data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node n))),
                                      (Vint (Int.repr (key_of_node n)),
                                       (Vint (Int.repr (value_of_node n)),
                                        (p_l, (p_r, p_par))))) p
         else emp)
.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ get_color1_spec ]).

Lemma body_get_color1: semax_body Vprog Gprog
                                    f_get_color1 get_color1_spec.
Proof.
  start_function.
  destruct b.
  + (* b = true *)
    assert_PROP (p <> nullval) by entailer!.
    forward_if. (* if (p == NULL) *)
    - congruence. (* p == NULL *)
    - forward.
      forward.
  + (* b = false *)
    assert_PROP (p = nullval).
    { entailer!.
      pose proof proj1 H eq_refl.
      auto. }
    forward_if. (* if (p == NULL) *)
    - forward. (* p == NULL *)
    - congruence.
Qed.

End getColor1.


(*  --------------------------------------------------------- *)

Module getColor2.

Definition get_color2_spec :=
  DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool
  PRE [tptr t_struct_tree]
    PROP (b = false <-> p = nullval)
    PARAMS (p)
    GLOBALS ()
    SEP (if b then
           rbtree_rep t p p_par
         else emp)
  POST [tint]
    PROP (b = false <-> p = nullval)
    RETURN ( Vint (Int.repr (
      if b then (* p <> nullval *)
        match t with
        | T _ n _ => Col2Z(color_of_node(n))
        | E => -2 (* unknown error *)
        end
      else -1)) )
    SEP (if b then
           rbtree_rep t p p_par
         else emp)
.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ get_color2_spec ]).

Lemma body_get_color2: semax_body Vprog Gprog
                                    f_get_color2 get_color2_spec.
Proof.
  start_function.
  destruct b.
  + (* b = true *)
    assert_PROP (p <> nullval).
    { entailer!.
      pose proof proj2 H eq_refl.
      congruence. }
    forward_if. (* if (p == NULL) *)
    - congruence. (* p == NULL *)
    - assert_PROP ( t <> E ).
      { entailer!. 
        pose proof proj2 H2 eq_refl.
        tauto. }
      destruct t as [|l n r] eqn:Et; [tauto|]. (* t = T l n r *)
      expand rbtree_rep.
      Intros p_lch p_rch.
      forward.
      forward.
      expand rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
  + (* b = false *)
    assert_PROP (p = nullval).
    { entailer!.
      pose proof proj1 H eq_refl.
      auto. }
    forward_if. (* if (p == NULL) *)
    - forward. (* p == NULL *)
    - congruence.
Qed.

End getColor2.

(* --------------------------------------------------------- *)
Module makeBlack.
Definition make_black_spec :=
  DECLARE _make_black
  WITH t_initial: tree,
       b_initial: val,
       p_par_initial: val
  PRE [ tptr (tptr t_struct_tree) ]
    PROP (b_initial <> nullval)
    PARAMS (b_initial)
    GLOBALS ()
    SEP (treebox_rep t_initial b_initial p_par_initial)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (treebox_rep (makeBlack t_initial) b_initial p_par_initial)
.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ make_black_spec ]).


Lemma body_make_black: semax_body Vprog Gprog
                                    f_make_black make_black_spec.
Proof.
  start_function.
  forward_if.
  + forward.
  + expand treebox_rep.
    Intros p_initial.
    forward.
    forward_if.
    - assert_PROP(t_initial = E).
      pose proof rbtree_rep_nullval t_initial p_par_initial.
      entailer!. tauto.
      forward.
      simpl. unfold treebox_rep, rbtree_rep. Exists nullval.
      entailer!.
    - assert_PROP(t_initial <> E).
      { destruct t_initial.
        { unfold rbtree_rep. entailer!. }
        { pose proof T_neq_E t_initial1 t_initial2 n.
          entailer!. } }
      destruct t_initial; [congruence|].
      unfold makeBlack.
      expand rbtree_rep.
      Intros p_lch p_rch.
      forward.
      expand treebox_rep.
      Exists p_initial.
      entailer!.
      expand rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
Qed.
End makeBlack.


(* --------------------------------------------------------- *)
Module leftRotate.

Definition left_rotate_spec :=
  DECLARE _left_rotate
  WITH p_l: val, 
       p_r: val,
       p_par: val,
       p_mid: val,
       p_l_l: val,
       p_r_r: val,
       l_n: Node,
       r_n: Node,
       tree_l_l: tree,
       tree_r_r: tree,
       tree_mid: tree
  PRE [ tptr t_struct_tree ]
    PROP (is_pointer_or_null p_par; 
          Int.min_signed <= key_of_node r_n <= Int.max_signed;
          Int.min_signed <= key_of_node l_n <= Int.max_signed)
    PARAMS (p_l)
    GLOBALS ()
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_r, p_par))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_mid, (p_r_r, p_l))))) p_r;
         rbtree_rep tree_mid p_mid p_r;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r )
  POST [ tptr t_struct_tree ]
    PROP (isptr p_r; p_r <> nullval;
          is_pointer_or_null p_par;
          Int.min_signed <= key_of_node r_n <= Int.max_signed;
          Int.min_signed <= key_of_node l_n <= Int.max_signed)
    RETURN (p_r)
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_mid, p_r))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_l, (p_r_r, p_par))))) p_r;
         rbtree_rep tree_mid p_mid p_l;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r ) (* p_par还连在p_l上 *)
.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ left_rotate_spec ]).

Lemma body_left_rotate: semax_body Vprog Gprog
                                    f_left_rotate left_rotate_spec.
Proof.
  start_function.
  forward. (* struct tree * r = l->right; *)
  forward. (* struct tree * mid = r->left; *)
  forward. 
  forward. (* r->left = l; *)
  forward.
  forward.
  forward. (* l->par = r; *)
  forward_if ( 
    PROP (isptr p_r; is_pointer_or_null p_par)
    LOCAL (temp _t'1 p_par; temp _mid p_mid; temp _r p_r; temp _l p_l)
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_mid, p_r))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_l, (p_r_r, p_par))))) p_r;
         rbtree_rep tree_mid p_mid p_l;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r )).
  + assert_PROP (tree_mid <> E) by (entailer!; tauto). (* mid != NULL *)
    destruct tree_mid eqn:tree_mid_fact; [congruence|]. (* tree_mid = T t1 n t2 *)
    expand rbtree_rep. (* rbtree_rep (T t1 n t2) p_mid p_r *)
    Intros p_mid_l p_mid_r.
    forward. (* mid->par = l; *)
    entailer!.
    expand rbtree_rep.
    Exists p_mid_l p_mid_r.
    entailer!.
  + forward. (* mid = NULL *)
    entailer!.
    assert (tree_mid = E) by tauto.
    subst.
    expand rbtree_rep.
    entailer!.
  + forward. (* return r; 证明r满足后条件 *)
Qed.

End leftRotate.


(* --------------------------------------------------------- *)
Module leftRotateWrap.

Definition left_rotate_wrap_spec := (* 就是为了处理p_l父亲的不同情况的 *)
  DECLARE _left_rotate_wrap
  WITH p_l: val, 
       p_r: val,
       p_par: val,
       p_mid: val,
       p_l_l: val,
       p_r_r: val,
       p_root: val,
       p_top: val,
       l_n: Node,
       r_n: Node,
       tree_l_l: tree,
       tree_r_r: tree,
       tree_mid: tree,
       root: val,
       b: bool,
       isleft: bool,
       p_gpar: val,
       p_unc: val,
       par_n: Node,
       uncisnull: bool,
       tree_unc: tree
  PRE [ tptr t_struct_tree, tptr (tptr t_struct_tree) ]
    PROP (nullval = p_par <-> b = false;
          Int.min_signed <= key_of_node r_n <= Int.max_signed;
          Int.min_signed <= key_of_node l_n <= Int.max_signed;
          p_top = nullval; p_l <> nullval;
          is_pointer_or_null p_par;
          is_pointer_or_null p_unc;
          p_unc <> p_l)
    PARAMS (p_l; root)
    GLOBALS ()
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_r, p_par))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_mid, (p_r_r, p_l))))) p_r;
         rbtree_rep tree_mid p_mid p_r;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r;
         if b then
           data_at Tsh (tptr t_struct_tree) p_root root *
           (if uncisnull then !! (p_unc = nullval) &&emp
             else rbtree_rep tree_unc p_unc p_par) *
           if isleft then
             data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_l, (p_unc, p_gpar))))) p_par
           else
             data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_unc, (p_l, p_gpar))))) p_par
         else
           data_at Tsh (tptr t_struct_tree) p_root root
         )
  POST [ tvoid ]
      PROP (nullval = p_par <-> b = false;
            isptr p_r; p_r <> nullval;
            Int.min_signed <= key_of_node r_n <= Int.max_signed;
            Int.min_signed <= key_of_node l_n <= Int.max_signed;
            is_pointer_or_null p_par;
            is_pointer_or_null p_unc;
            p_unc <> p_l)
      RETURN ()
      SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                      (Vint (Int.repr (key_of_node l_n)),
                                       (Vint (Int.repr (value_of_node l_n)),
                                        (p_l_l, (p_mid, p_r))))) p_l;
           data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                      (Vint (Int.repr (key_of_node r_n)),
                                       (Vint (Int.repr (value_of_node r_n)),
                                        (p_l, (p_r_r, p_par))))) p_r;
           rbtree_rep tree_mid p_mid p_l;
           rbtree_rep tree_l_l p_l_l p_l;
           rbtree_rep tree_r_r p_r_r p_r;
           if b then
             data_at Tsh (tptr t_struct_tree) p_root root *
             (if uncisnull then !! (p_unc = nullval) &&emp
               else rbtree_rep tree_unc p_unc p_par) *
             if isleft then
               data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_r, (p_unc, p_gpar))))) p_par
             else
               data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_unc, (p_r, p_gpar))))) p_par
           else
             data_at Tsh (tptr t_struct_tree) p_r root )
.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ leftRotate.left_rotate_spec; left_rotate_wrap_spec ]).
         
Lemma body_left_rotate_wrap: semax_body Vprog Gprog
                                    f_left_rotate_wrap left_rotate_wrap_spec.
Proof.
  start_function.
  subst p_top.
  (* assert_PROP (is_pointer_or_null p_par) by entailer!. *)
  forward.
  forward_if.
  { destruct b. destruct isleft; entailer!.
    assert (nullval = p_par) by tauto.
    entailer!. }
  + destruct b.
    { subst p_par. assert(true = false) by tauto.
      congruence. }
    forward_call(p_l, p_r, (* l->par == NULL *)
        p_par, p_mid,
        p_l_l, p_r_r,
        l_n, r_n,
        tree_l_l, tree_r_r, tree_mid).
    forward.
    entailer!.
  + destruct b.
    2: { assert(nullval = p_par) by tauto. congruence. }
    destruct isleft; destruct uncisnull; Intros;
    forward; forward; forward_if_wrp; try contradiction; 
    forward_call(p_l, p_r, 
        p_par, p_mid,
        p_l_l, p_r_r,
        l_n, r_n,
        tree_l_l, tree_r_r, tree_mid);
    forward; entailer!.
Qed.

End leftRotateWrap.


(* --------------------------------------------------------- *)
Module rightRotate.

Definition right_rotate_spec :=
  DECLARE _right_rotate
  WITH p_l: val, 
       p_r: val,
       p_par: val,
       p_mid: val,
       p_l_l: val,
       p_r_r: val,
       l_n: Node,
       r_n: Node,
       tree_l_l: tree,
       tree_r_r: tree,
       tree_mid: tree
  PRE [ tptr t_struct_tree ]
    PROP (is_pointer_or_null p_par; 
          Int.min_signed <= key_of_node l_n <= Int.max_signed;
          Int.min_signed <= key_of_node r_n <= Int.max_signed)
    PARAMS (p_r)
    GLOBALS ()
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_mid, p_r))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_l, (p_r_r, p_par))))) p_r;
         rbtree_rep tree_mid p_mid p_l;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r )
  POST [ tptr t_struct_tree ]
    PROP (isptr p_l; p_l <> nullval;
          is_pointer_or_null p_par;
          Int.min_signed <= key_of_node r_n <= Int.max_signed;
          Int.min_signed <= key_of_node l_n <= Int.max_signed)
    RETURN (p_l)
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_r, p_par))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_mid, (p_r_r, p_l))))) p_r;
         rbtree_rep tree_mid p_mid p_r;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r )
.
Definition Gprog : funspecs :=
         ltac:(with_library prog [ right_rotate_spec ]).

Lemma body_right_rotate: semax_body Vprog Gprog
                                    f_right_rotate right_rotate_spec.
Proof.
  start_function.
  forward.
  forward.
  forward. 
  forward.
  forward.
  forward.
  forward.
  forward_if ( 
    PROP (isptr p_l; is_pointer_or_null p_par)
    LOCAL (temp _t'1 p_par; temp _mid p_mid; temp _r p_r; temp _l p_l)
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_r, p_par))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_mid, (p_r_r, p_l))))) p_r;
         rbtree_rep tree_mid p_mid p_r;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r )).
  + assert_PROP (tree_mid <> E) by (entailer!; tauto).
    destruct tree_mid eqn:tree_mid_fact; [congruence|]. 
    expand rbtree_rep.
    Intros p_mid_l p_mid_r.
    forward.
    entailer!.
    expand rbtree_rep.
    Exists p_mid_l p_mid_r.
    entailer!.
  + forward. (* mid = NULL *)
    entailer!.
    assert (tree_mid = E) by tauto.
    subst.
    expand rbtree_rep.
    entailer!.
  + forward.
Qed.

End rightRotate.


(* --------------------------------------------------------- *)
Module rightRotateWrap.


Definition right_rotate_wrap_spec := (* 就是为了处理p_r父亲的不同情况的 *)
  DECLARE _right_rotate_wrap
  WITH p_l: val, 
       p_r: val,
       p_par: val,
       p_mid: val,
       p_l_l: val,
       p_r_r: val,
       p_root: val,
       p_top: val,
       l_n: Node,
       r_n: Node,
       tree_l_l: tree,
       tree_r_r: tree,
       tree_mid: tree,
       root: val,
       b: bool,
       isleft: bool,
       p_gpar: val,
       p_unc: val,
       par_n: Node,
       uncisnull: bool,
       tree_unc: tree
  PRE [ tptr t_struct_tree, tptr (tptr t_struct_tree) ]
    PROP (nullval = p_par <-> b = false;
          Int.min_signed <= key_of_node l_n <= Int.max_signed;
          Int.min_signed <= key_of_node r_n <= Int.max_signed;
          p_r <> nullval; p_top = nullval;
          is_pointer_or_null p_par;
          is_pointer_or_null p_unc;
          p_unc <> p_r)
    PARAMS (p_r; root)
    GLOBALS ()
    SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                    (Vint (Int.repr (key_of_node l_n)),
                                     (Vint (Int.repr (value_of_node l_n)),
                                      (p_l_l, (p_mid, p_r))))) p_l;
         data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                    (Vint (Int.repr (key_of_node r_n)),
                                     (Vint (Int.repr (value_of_node r_n)),
                                      (p_l, (p_r_r, p_par))))) p_r;
         rbtree_rep tree_mid p_mid p_l;
         rbtree_rep tree_l_l p_l_l p_l;
         rbtree_rep tree_r_r p_r_r p_r;
         if b then
           data_at Tsh (tptr t_struct_tree) p_root root *
           (if uncisnull then !! (p_unc = nullval) && emp
               else rbtree_rep tree_unc p_unc p_par) *
           if isleft then
             data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_r, (p_unc, p_gpar))))) p_par
           else
             data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_unc, (p_r, p_gpar))))) p_par
         else
           data_at Tsh (tptr t_struct_tree) p_root root
         )
  POST [ tvoid ]
      PROP (nullval = p_par <-> b = false; 
            Int.min_signed <= key_of_node l_n <= Int.max_signed;
            Int.min_signed <= key_of_node r_n <= Int.max_signed;
            is_pointer_or_null p_par;
            is_pointer_or_null p_unc;
            p_unc <> p_r)
      RETURN ()
      SEP (data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node l_n))),
                                      (Vint (Int.repr (key_of_node l_n)),
                                       (Vint (Int.repr (value_of_node l_n)),
                                        (p_l_l, (p_r, p_par))))) p_l;
           data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node r_n))),
                                      (Vint (Int.repr (key_of_node r_n)),
                                       (Vint (Int.repr (value_of_node r_n)),
                                        (p_mid, (p_r_r, p_l))))) p_r;
           rbtree_rep tree_mid p_mid p_r;
           rbtree_rep tree_l_l p_l_l p_l;
           rbtree_rep tree_r_r p_r_r p_r;
           if b then
             data_at Tsh (tptr t_struct_tree) p_root root *
             (if uncisnull then !! (p_unc = nullval) && emp
               else rbtree_rep tree_unc p_unc p_par) *
             if isleft then
               data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_l, (p_unc, p_gpar))))) p_par
             else
               data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node par_n))),
                                        (Vint (Int.repr (key_of_node par_n)),
                                         (Vint (Int.repr (value_of_node par_n)),
                                          (p_unc, (p_l, p_gpar))))) p_par
           else
             data_at Tsh (tptr t_struct_tree) p_l root )
.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ rightRotate.right_rotate_spec; right_rotate_wrap_spec ]).

Lemma body_right_rotate_wrap: semax_body Vprog Gprog
                                    f_right_rotate_wrap right_rotate_wrap_spec.
Proof.
  start_function.
  subst p_top.
  (* assert_PROP (is_pointer_or_null p_par) by entailer!. *)
  forward.
  forward_if.
  { destruct b. destruct isleft; entailer!.
    assert (nullval = p_par) by tauto.
    entailer!. }
  + destruct b.
    { subst p_par. assert(true = false) by tauto.
      congruence. }
    forward_call(p_l, p_r, (* l->par == NULL *)
        p_par, p_mid,
        p_l_l, p_r_r,
        l_n, r_n,
        tree_l_l, tree_r_r, tree_mid).
    forward.
    entailer!.
  + destruct b.
    2: { assert(nullval = p_par) by tauto. congruence. }
    destruct isleft, uncisnull; Intros;
    forward; forward; forward_if_wrp; try contradiction; try solve[
    forward_call(p_l, p_r, 
        p_par, p_mid,
        p_l_l, p_r_r,
        l_n, r_n,
        tree_l_l, tree_r_r, tree_mid);
    forward; entailer!].
Qed.

End rightRotateWrap.
