Require Import VST.floyd.proofauto.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Export RBTree.rbt_insert2.
Require Export RBTree.dependency.RTClosure.
Require Export RBTree.Tacs.
Require Import RBTree.AuxiliaryTac.
Require Import Coq.Logic.Classical.
Import ListNotations.
Local Open Scope Z.

Definition Key: Type := Z.
Definition Value: Type := Z.
Inductive color := Red | Black.

Record Node  := {
   color_of_node : color;
   key_of_node : Key;
   value_of_node : Value
}.

Inductive tree : Type :=
| E : tree
| T : tree -> Node -> tree -> tree.

Inductive LeftOrRight :=
| L: LeftOrRight
| R: LeftOrRight.
(* 可以通过partial_tree以复原原树 *)

Definition half_tree: Type := (LeftOrRight * Node * tree)%type.

Definition partial_tree: Type := list half_tree.

Fixpoint insert_split (x: Key) (s : tree) (b: partial_tree): partial_tree * tree :=
  match s with
  | E => (b, E)
  | T l n r =>
    if x <? key_of_node n
    then insert_split x l ((R, n, r) :: b)
    else if x >? key_of_node n
         then insert_split x r ((L, n, l) :: b) (* "modified" *)
         else (b, s)
  end.

(* e.g.

          n
  s:    /   \      &&     x <? Key(n)  ==>>   (R, n, r) is appended to b.
       l     r
  若l是空树, 则返回值(b, E), E是被插入的位置;
  若l是非空树, 则返回值(b, s), s是被插入的位置.
  使得通过E/s, b可以可以复原原树, 只需要依次从b中读取头部数据即可.
  读取(R, n, r)即表示, 可以通过给当前树添加父亲n和右(R)儿子r, 同时消去b的首个元素, 来逐步恢复树.
  也就是 "complete_tree" 所说的那样.
*)


Definition insert_root (x: Key) (v: Value) (s: tree) : tree :=
  match s with
  | E => T E (Build_Node Red x v) E (* 新插入节点默认为"红色", 原因:着成黑色, 则该路径上黑色节点数必不平衡, 调整起来太复杂, 不可取 *)
  | T l n r =>  T l (Build_Node (color_of_node n) x v) r (* 不改变原根颜色 *)
  end.
(* Build_Node是record Node的构造函数 *)


Definition l_rotate x a yz :=
  match yz with
  | E => E
  | T y b z =>  T (T x a y) b z
  end.

Definition r_rotate xy b z :=
  match xy with
  | E => E
  | T x a y =>  T x a (T y b z)
  end.

(* 
         a          "l_rotate"        b
        / \         ==========>      / \
       x   b                        a   z
          / \      <==========     / \
         y   z      "r_rotate"    x   y
*)

Definition RedNode n: Node := (* Rednodalify Node n *)
  Build_Node Red (key_of_node n) (value_of_node n).

Definition BlackNode n: Node := (* Blacknodalify Node n *)
  Build_Node Black (key_of_node n) (value_of_node n).

Definition makeBlack t := (* Blacknodalify the root of BRTree t*)
  match t with 
  | E => E
  | T a n b => T a (BlackNode n) b
  end.

Definition Red_tree s := (* 指标函数 *)
  match s with
  | T _ (Build_Node Red _ _) _ => True (* 根节点是红色 *)
  | _ => False (* 空树, 或者根节点是黑色 *)
  end.

Definition Black_tree s :=
  match s with
  | T _ (Build_Node Black _ _) _ => True
  | _ => False
  end.

Fixpoint balance'  (l: partial_tree) (s: tree) : partial_tree * tree  :=
(* 插入后, partial_tree不变; s变为insert_root后的树; 若插入点s为红色, 则传入balance'调整*)
  match l with
  (**插入结点前为空树*)
  | nil => (nil,  s) 
  (**插入点为根节点的儿子*) (* 有兄弟的话, 那么这个兄弟必然是没有儿子的红色节点; 且根节点为黑色 *)
  | _::nil => (l , s) (* 不需要调整 *)
  (**插入点有父亲和祖父*)
  | (pLR, pn, brother) :: (gLR, gn, uncle) :: l' =>
    (*父亲结点为黑色则不变，为红色需要调整*)
    match color_of_node pn with
    | Black => (l, s)
    | Red =>
      (* 此时祖父节点一定为黑色
         分情况当前结点为父亲结点的左子还是右子*)
      match pLR with
      | R =>
        (* 左子 *)
        (**讨论叔叔结点的颜色*)
        match uncle with
        | T a (Build_Node Red u uv) b => 
          (**讨论叔叔节点为左子还是右子*)
          (* 将父节点和叔叔节点涂黑，祖父节点涂红指向祖父节点进行平衡 *)
          match gLR with
          | R =>                                                             (*checked*)
            (* 右子 *)
            balance' l' (T (T s (BlackNode pn) brother) (RedNode gn) (makeBlack uncle))
          | L => 
            (* 左子 *)
            balance' l' (T (makeBlack uncle) (RedNode gn) (T s (BlackNode pn) brother))
          end
        | _ => 
          (**讨论叔叔节点为左子还是右子*)
          match gLR with 
          | R => (*父节点染黑，祖父染红，祖父为支点右旋*)                            (*checked*)
            (l', r_rotate (T s (BlackNode pn) brother) (RedNode gn) uncle) 
          | L => (*先以父节点为支点右旋，把我染黑祖父染红，祖父为支点左旋*)        (*checked*)
            (l', l_rotate uncle (RedNode gn)
                   (r_rotate (makeBlack s) pn brother) )
          end
        end
      | L =>
        (* 右子 *)
        (**讨论叔叔结点的颜色*)
        match uncle with
        | T a (Build_Node Red u uv) b => 
          (**讨论叔叔节点为左子还是右子*)
          (*将父节点和叔叔节点涂黑，祖父节点涂红指向祖父节点进行平衡*)
          match gLR with
          | R =>
            (* 右子 *)
            balance' l' (T (T brother (BlackNode pn) s) (RedNode gn) (makeBlack uncle))
          | L =>
            (* 左子 *)
            balance' l' (T (makeBlack uncle) (RedNode gn) (T brother (BlackNode pn) s))
          end
        | _ =>
          (**讨论叔叔节点为左子还是右子*)
          match gLR with 
          | R => (*先以父节点为支点左旋，把我染黑祖父染红，祖父为支点右旋*)
             (l', r_rotate (l_rotate brother pn (makeBlack s)) (RedNode gn) uncle)
          | L => (*父节点染黑，祖父染红，祖父为支点左旋*)
             (l', l_rotate uncle (RedNode gn) (T brother (BlackNode pn) s))
          end
        end
      end
    end
  end.

Fixpoint complete_tree  (l: partial_tree) (b : tree) : tree := (* 还原树 *)
match l with
| nil => b
| (pLR, pn, brother) :: l' =>
  (*当前子树base为左子树还是右*)
  match pLR with
  | R => complete_tree l' (T b pn brother)
  | L => complete_tree l' (T brother pn b)
  end
end.

Inductive insert k v t : tree -> Prop :=
| insert_intro_Red : forall l s h b,
    (l, s) = insert_split k t nil -> (* insert_split计算出的插入点为s, 对应的partial_tree为l *)
    Red_tree (insert_root k v s) -> (* 在s处insert_root后为红色 [s为EMPTY或原本为红节点] *)
    (h, b) = balance' l (insert_root k v s) -> (* 只有insert_root的颜色为红色时才需要调整 *)
    insert k v t (makeBlack (complete_tree h b))
| insert_intro_Black : forall l s,
    (l, s) = insert_split k t nil ->
    Black_tree (insert_root k v s) ->
    insert k v t (makeBlack (complete_tree l (insert_root k v s)))
.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree : type := Tstruct _tree noattr.

Definition RED_COLOR : Z := 1.        (* """" *)
Definition BLACK_COLOR : Z := 0.      (* """" *)

Definition Col2Z (c : color) : Z :=
  match c with
  | Red   => RED_COLOR
  | Black => BLACK_COLOR
  end.

(* ----------------------------------------------------------- *)
Lemma T_neq_E:
  forall t1 t2 n, T t1 n t2 <> E.
Proof. 
  intros. pose proof classic (T t1 n t2 = E).
  destruct H; congruence.
Qed.

Lemma insert_root_neq_E:
  forall k v s,
    insert_root k v s <> E.
Proof.
  intros. destruct s; apply T_neq_E.
Qed.

(* ----------------------------------------------------------- *)
(* ----------------------------------------------------------- *)
Fixpoint rbtree_rep (t : tree) (p p_par : val) : mpred :=
                                 (* parent *)
  (* rbtree由三个变量表示: tree和其指针, 父亲指针 *)
  (* 存储以p为根的一整棵树 *)
  match t with
  | T lch n rch =>
   (* lchild|rchild:tree; n:Node *)
    !! (Int.min_signed <= key_of_node n <= Int.max_signed /\ 
      is_pointer_or_null p_par) &&
    EX p_lch : val, EX p_rch : val, 
    data_at Tsh t_struct_tree (* t_struct_tree由六元组组成: (Node_triple, 左右孩子地址, 父亲地址) *)
      ( Vint (Int.repr (Col2Z (color_of_node n))) ,
        ( Vint (Int.repr (key_of_node n)) ,
          (Vint (Int.repr (value_of_node n)) ,
              (p_lch, (p_rch, p_par))))) p (* 存储于地址p *)
    * rbtree_rep lch p_lch p * rbtree_rep rch p_rch p
  | E => !! (p = nullval /\ is_pointer_or_null p_par) && emp 
  end.

Lemma rbtree_rep_local_facts:
  forall t p p_par,
    rbtree_rep t p p_par |-- 
    !! ( is_pointer_or_null p     /\ 
         is_pointer_or_null p_par /\
         (p = nullval <-> t = E) ).
Proof.
  intro t.
  induction t; intros p p_par;
    expand rbtree_rep; entailer; entailer!.
  + split; auto.
  + split; intro.
    ++ subst p.
       eapply field_compatible_nullval; eauto.
    ++ inv H4.
Qed.
Hint Resolve rbtree_rep_local_facts : saturate_local.

Lemma rbtree_rep_valid_pointer:
  forall t p p_par,
    rbtree_rep t p p_par |-- valid_pointer p. 
Proof.
  intros.
  unfold rbtree_rep.
  destruct t; simpl; entailer.
Qed.
Hint Resolve rbtree_rep_valid_pointer : valid_pointer.

Lemma rbtree_rep':
  forall (p: val) (p_l: val) (p_r: val) (p_par: val) (lch: tree) (rch: tree) (n: Node),
    is_pointer_or_null p_par ->
    Int.min_signed <= key_of_node n <= Int.max_signed ->
       data_at Tsh t_struct_tree
         (Vint (Int.repr (Col2Z (color_of_node n))),
         (Vint (Int.repr (key_of_node n)),
         (Vint (Int.repr (value_of_node n)), (p_l, (p_r, p_par))))) p *
       rbtree_rep lch p_l p * rbtree_rep rch p_r p
    |-- 
    rbtree_rep (T lch n rch) p p_par.
Proof.
  intros.
  expand rbtree_rep.
  Exists p_l p_r. entailer!.
Qed.

Lemma rbtree_rep_nullval: forall t p_par,
  rbtree_rep t nullval p_par |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer!|].
  expand rbtree_rep.
  Intros a b. entailer!.
Qed.

(* ----------------------------------------------------------- *)

Ltac solve_field_compatible :=
  repeat
  match goal with
  | H: field_compatible ?t (StructField ?f :: ?gfs) ?p |- _ =>
    let HH := fresh "H" in
    pose proof H as HH; revert H;
    rewrite field_compatible_cons in HH;
    simpl in HH;
    destruct HH
  end;
  intros;
  auto with field_compatible.

(* ----------------------------------------------------------- *)
(** For treeboxes. *)
Definition treebox_rep (t : tree) (b p_par : val) := (* b是二级指针? *)
  EX p : val, data_at Tsh (tptr t_struct_tree) p b * rbtree_rep t p p_par.
  (* 数据类型(tptr t_struct_tree), 值p, 地址b; 所以b是二级指针 *)
  (* treebox由tree和其二级指针, 父亲指针表示 *)
  (* 存储以b为根的地址的一整棵树, 和根的地址p *)
Lemma treebox_rep_local_facts:
  forall t b p_par,
    treebox_rep t b p_par |--
    !! ( is_pointer_or_null b   /\
         is_pointer_or_null p_par ).
Proof.
  intro t.
  induction t; intros b p_par;
    expand treebox_rep; entailer; entailer!.
Qed.
Hint Resolve treebox_rep_local_facts : saturate_local.
  
Lemma treebox_rep_valid_pointer:
  forall t b p_par,
    treebox_rep t b p_par |-- valid_pointer b.
Proof.
  intros.
  unfold treebox_rep.
  destruct t; simpl; entailer.
Qed.
Hint Resolve treebox_rep_valid_pointer : valid_pointer.

Lemma treebox_rep_l:
  forall (p_par: val) (p_gpar: val) (p_sib: val) (ts: tree) (t: tree) (n: Node) (b_par: val),
    is_pointer_or_null p_gpar ->
    Int.min_signed <= key_of_node n <= Int.max_signed ->
       data_at Tsh (tptr t_struct_tree) p_par b_par *
       field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node n)))) p_par *
       field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node n))) p_par *
       field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node n))) p_par *
       field_at Tsh t_struct_tree [StructField _left] p_sib p_par *
       field_at Tsh t_struct_tree [StructField _par] p_gpar p_par *
       treebox_rep t (field_address t_struct_tree [StructField _right] p_par) p_par *
       rbtree_rep ts p_sib p_par
  |--  treebox_rep (T ts n t) b_par p_gpar.
Proof.
  intros.
  expand treebox_rep.
  Intros p. Exists p_par.
  expand rbtree_rep.
  Exists p_sib p. entailer!.
  unfold_data_at (data_at _ t_struct_tree _ p_par). entailer!.
Qed.

Lemma treebox_rep_r:
  forall (p_par: val) (p_gpar: val) (p_sib: val) (t: tree) (ts: tree) (n: Node) (b_par: val),
    is_pointer_or_null p_gpar ->
    Int.min_signed <= key_of_node n <= Int.max_signed ->
       data_at Tsh (tptr t_struct_tree) p_par b_par *
       field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node n)))) p_par *
       field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node n))) p_par *
       field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node n))) p_par *
       field_at Tsh t_struct_tree [StructField _right] p_sib p_par *
       field_at Tsh t_struct_tree [StructField _par] p_gpar p_par *
       treebox_rep t (field_address t_struct_tree [StructField _left] p_par) p_par *
       rbtree_rep ts p_sib p_par
  |--  treebox_rep (T t n ts) b_par p_gpar.
Proof.
  intros.
  expand treebox_rep.
  Intros p. Exists p_par.
  expand rbtree_rep.
  Exists p p_sib. entailer!.
  unfold_data_at (data_at _ t_struct_tree _ p_par). entailer!.
Qed.

Lemma treebox_rep_lr:
  forall (p: val) (p_l: val) (p_r: val) (p_par: val) (t_l: tree) (t_r: tree) (n: Node) (b: val),
    is_pointer_or_null p_par ->
    Int.min_signed <= key_of_node n <= Int.max_signed ->
      data_at Tsh (tptr t_struct_tree) p b *
      data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node n))),
                                 (Vint (Int.repr (key_of_node n)),
                                  (Vint (Int.repr (value_of_node n)),
                                   (p_l, (p_r, p_par))))) p *
      rbtree_rep t_l p_l p * rbtree_rep t_r p_r p
  |-- treebox_rep (T t_l n t_r) b p_par.
Proof.
  intros.
  expand treebox_rep.
  expand rbtree_rep.
  Exists p p_l p_r. entailer!.
Qed.

(* ----------------------------------------------------------- *)


(* ----------------------------------------------------------- *)
(** For partial trees. *)
Fixpoint partial_tree_rep (t : partial_tree) (p_root p p_par p_top : val) : mpred :=
  (* 存储(以p为根的树)的补集的所有值,一级指针信息 *)
  match t with     (* p_root和p_top分别表示全树的根和根的父亲 *)
  | [] => !! (p = p_root /\ p_par = p_top) && emp
             (* 当前指针指向根, 父亲指针指向根的父亲 *)
  | (L, n, lch) :: l =>
    EX p_gpar: val, EX p_sib : val,
        !! (Int.min_signed <= key_of_node n <= Int.max_signed) &&
        rbtree_rep lch p_sib p_par *
        partial_tree_rep l p_root p_par p_gpar p_top *
        data_at Tsh t_struct_tree
        (Vint (Int.repr (Col2Z (color_of_node n))),
          (Vint (Int.repr (key_of_node n)),
            (Vint (Int.repr (value_of_node n)), (p_sib, (p, p_gpar))))) p_par
  | (R, n, rch) :: l =>
    EX p_gpar: val, EX p_sib : val, 
        !! (Int.min_signed <= key_of_node n <= Int.max_signed) &&
        rbtree_rep rch p_sib p_par *
        partial_tree_rep l p_root p_par p_gpar p_top *
        data_at Tsh t_struct_tree
        (Vint (Int.repr (Col2Z (color_of_node n))), 
          (Vint (Int.repr (key_of_node n)),
            (Vint (Int.repr (value_of_node n)), (p, (p_sib, p_gpar))))) p_par
  end.

Lemma partial_tree_rep_local_facts:
  forall t p_root p p_par,
    partial_tree_rep t p_root p p_par nullval |--
    !! ( is_pointer_or_null p_par ).
Proof.
  intro t.
  induction t; intros.
  + expand partial_tree_rep.
    entailer!.
  + destruct a as [[L_or_R N] Tree_Lsib_Or_Rsib]; destruct L_or_R;
    expand partial_tree_rep; Intros p_gpar p_sib; entailer!.
Qed.
Hint Resolve partial_tree_rep_local_facts : saturate_local.

(* ----------------------------------------------------------- *)
Fixpoint partial_tree_rep_topdown (rev_t : partial_tree) (p_root p p_par p_top : val) : mpred :=
match rev_t with
| nil => !! (p = p_root /\ p_par = p_top) && emp
| (LR, node_ans, tree_ans_another_child) :: l => 
    EX p_ans_another_child: val, EX p_ans_child,
      !! (Int.min_signed <= key_of_node node_ans <= Int.max_signed) &&
      rbtree_rep tree_ans_another_child p_ans_another_child p_root *
      field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node node_ans)))) p_root *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node node_ans))) p_root *
      field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node node_ans))) p_root * (* 父亲的节点信息 *)
      field_at Tsh t_struct_tree [StructField _par] p_top p_root *
      match LR with
      | L => field_at Tsh t_struct_tree [StructField _left] p_ans_another_child p_root *
             field_at Tsh t_struct_tree [StructField _right] p_ans_child p_root *
             partial_tree_rep_topdown l p_ans_child p p_par p_root
      | R => field_at Tsh t_struct_tree [StructField _right] p_ans_another_child p_root *
             field_at Tsh t_struct_tree [StructField _left] p_ans_child p_root *
             partial_tree_rep_topdown l p_ans_child p p_par p_root
  end 
end.

(* append singleton *)
Lemma partial_tree_rep_topdown_sgt
  (rev_t : partial_tree) (p_root p p_par p_top : val) (lr: LeftOrRight) (nd: Node) (tr: tree) :
partial_tree_rep_topdown (rev_t ++ [(lr, nd, tr)]) p_root p p_par p_top = 
  EX p_gpar: val, EX p_sib: val,
    !! (Int.min_signed <= key_of_node nd <= Int.max_signed) &&
    partial_tree_rep_topdown rev_t p_root p_par p_gpar p_top *
    field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node nd)))) p_par *
    field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node nd))) p_par *
    field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node nd))) p_par *
    field_at Tsh t_struct_tree [StructField _par] p_gpar p_par *
    rbtree_rep tr p_sib p_par *
    match lr with
    | L => field_at Tsh t_struct_tree [StructField _right] p p_par *
           field_at Tsh t_struct_tree [StructField _left] p_sib p_par
    | R => field_at Tsh t_struct_tree [StructField _left] p p_par *
           field_at Tsh t_struct_tree [StructField _right] p_sib p_par
    end.
Proof.
  revert p_root p p_par p_top.
  induction rev_t as [|[[LRr Ndr] Trr]]; intros.
  + apply pred_ext; simpl.
    - Intros p_ans_another_child p_child.
      destruct lr; Exists p_top p_ans_another_child; entailer!.
    - Intros p_gpar p_sib. 
      destruct lr; Exists p_sib p; entailer!; solve_field_compatible.
  + apply pred_ext; simpl.
    - Intros p_ans_another_child p_child.
      destruct LRr, lr; rewrite IHrev_t;
      Intros p_gpar p_sib;
      Exists p_gpar p_sib p_ans_another_child p_child; entailer!.
    - Intros p_gpar p_sib p_ans_another_child p_child.
      destruct LRr, lr;
      Exists p_ans_another_child p_child;
      rewrite IHrev_t;
      Exists p_gpar p_sib; entailer!.
Qed.

Lemma partial_tree_rep' (t : partial_tree) (p_root p p_par p_top : val):
  partial_tree_rep t p_root p p_par p_top = 
  partial_tree_rep_topdown (rev t) p_root p p_par p_top.
Proof.
  revert p_root p p_par p_top.
  induction t as [|[[LR Nd] Tr]]; intros.
  + reflexivity.
  + simpl rev. 
    rewrite partial_tree_rep_topdown_sgt.
    expand partial_tree_rep.
    apply pred_ext; destruct LR;
    Intros p_gpar p_sib; (rewrite IHt || rewrite <- IHt);
    Exists p_gpar p_sib; entailer!;
    unfold_data_at (data_at _ t_struct_tree _ p_par); entailer!.
Qed.

(* ----------------------------------------------------------- *)


(** For partial treeboxes. *)
Fixpoint partial_treebox_rep (t : partial_tree) (root b p_par p_top : val) : mpred :=
  match t with
  | [] => !! (p_par = p_top /\ root = b /\ is_pointer_or_null root) && emp 
  | (L, n, lch) :: l =>
    EX p_gpar: val, EX p_sib : val, EX b_par : val,
      !! (Int.min_signed <= key_of_node n <= Int.max_signed) &&
      !! (b = field_address t_struct_tree [StructField _right] p_par) && (* b是p_par的右儿子的地址 *)
      rbtree_rep lch p_sib p_par *
      field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node n)))) p_par *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node n))) p_par *
      field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node n))) p_par *
      field_at Tsh t_struct_tree [StructField _left] p_sib p_par *
      field_at Tsh t_struct_tree [StructField _par] p_gpar p_par *
      data_at Tsh (tptr t_struct_tree) p_par b_par *
      partial_treebox_rep l root b_par p_gpar p_top
  | (R, n, rch) :: l =>
    EX p_gpar: val, EX p_sib : val, EX b_par : val,
      !! (Int.min_signed <= key_of_node n <= Int.max_signed) &&
      !! (b = field_address t_struct_tree [StructField _left] p_par) &&
      rbtree_rep rch p_sib p_par *
      field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node n)))) p_par *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node n))) p_par *
      field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node n))) p_par *
      field_at Tsh t_struct_tree [StructField _right] p_sib p_par *
      field_at Tsh t_struct_tree [StructField _par] p_gpar p_par *
      data_at Tsh (tptr t_struct_tree) p_par b_par *
      partial_treebox_rep l root b_par p_gpar p_top
  end.

(* ----------------------------------------------------------- *)

Lemma partial_treebox_rep_local_facts:
  forall t root b p_par,
    partial_treebox_rep t root b p_par nullval |--
    !! ( is_pointer_or_null p_par /\
         is_pointer_or_null root /\
         is_pointer_or_null b ).
Proof.
  intro t.
  induction t; intros root b p_par.
  + expand partial_treebox_rep.
    entailer!.
  + destruct a as [[L_or_R N] Tree_Lsib_Or_Rsib]; destruct L_or_R;
    expand partial_treebox_rep; Intros p_gpar p_sib b_par;
    pose proof (IHt root b_par p_gpar); entailer!; solve_field_compatible.
Qed.
Hint Resolve partial_treebox_rep_local_facts : saturate_local.


Lemma partial_treebox_rep_local_facts_top:
  forall t root b p_par p_top,
    partial_treebox_rep t root b p_par p_top |--
    !! ( is_pointer_or_null root /\
         is_pointer_or_null b ).
Proof.
  intro t.
  induction t; intros root b p_par p_top.
  + expand partial_treebox_rep.
    entailer!.
  + destruct a as [[L_or_R N] Tree_Lsib_Or_Rsib]; destruct L_or_R;
    expand partial_treebox_rep; Intros p_gpar p_sib b_par;
    pose proof (IHt root b_par p_gpar); entailer!; solve_field_compatible.
Qed.

(* ----------------------------------------------------------- *)

(* 等价定义1 *)
Lemma partial_treebox_rep' (t : partial_tree) (root b p_par p_top : val):
partial_treebox_rep t root b p_par p_top = (* 保存了以*b为根的树的补集的全部二级指针\一级指针\值信息, 但是同样传入了b信息 *)
  match t with (* 可以在不讨论LR的情况下, 就能给出一定的信息 *)
  | nil => !! (p_par = p_top /\ root = b /\ is_pointer_or_null root) && emp
  | (LR, n, ch) :: l =>
      EX p_gpar: val, EX p_sib : val, EX b_par : val,
          !! (Int.min_signed <= key_of_node n <= Int.max_signed) &&
          rbtree_rep ch p_sib p_par * (* 侄子及其子树信息 *)
          field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node n)))) p_par *
          field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node n))) p_par *
          field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node n))) p_par * (* 父亲的节点信息 *)
          field_at Tsh t_struct_tree [StructField _par] p_gpar p_par * (* 父亲的父亲的地址信息 *)
          data_at Tsh (tptr t_struct_tree) p_par b_par * (* 父亲的二级指针 *)
          partial_treebox_rep l root b_par p_gpar p_top *
          match LR with
          | L => !! (b = field_address t_struct_tree [StructField _right] p_par) &&
                 field_at Tsh t_struct_tree [StructField _left] p_sib p_par
          | R => !! (b = field_address t_struct_tree [StructField _left] p_par) &&
                 field_at Tsh t_struct_tree [StructField _right] p_sib p_par
         end
     end.
Proof.
  destruct t as [|[[Cl Nd] Tr]]; expand partial_treebox_rep; auto.
  destruct Cl; apply pred_ext; Intros p_gpar p_sib b_par; Exists p_gpar p_sib b_par; entailer!.
Qed.

(* 等价定义2 *)
Fixpoint partial_treebox_rep_topdown (rev_t : partial_tree) (root b p_par p_top : val): mpred :=
match rev_t with
| nil => !! (p_par = p_top /\ root = b /\ is_pointer_or_null root) && emp
| (LR, node_ans, tree_ans_another_child) :: l => 
    EX p_ans_another_child: val, EX p_ans: val,
      !! (Int.min_signed <= key_of_node node_ans <= Int.max_signed) &&
      rbtree_rep tree_ans_another_child p_ans_another_child p_ans *
      field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node node_ans)))) p_ans *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node node_ans))) p_ans *
      field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node node_ans))) p_ans * (* 父亲的节点信息 *)
      field_at Tsh t_struct_tree [StructField _par] p_top p_ans *
      data_at Tsh (tptr t_struct_tree) p_ans root *
      match LR with
      | L => field_at Tsh t_struct_tree [StructField _left] p_ans_another_child p_ans *
             partial_treebox_rep_topdown l (field_address t_struct_tree [StructField _right] p_ans) b p_par p_ans
      | R => field_at Tsh t_struct_tree [StructField _right] p_ans_another_child p_ans *
             partial_treebox_rep_topdown l (field_address t_struct_tree [StructField _left] p_ans) b p_par p_ans
  end 
end.

(* append singleton *)
Lemma partial_treebox_rep_topdown_sgt
  (rev_t : partial_tree) (root b p_par p_top : val) (lr: LeftOrRight) (nd: Node) (tr: tree) :
partial_treebox_rep_topdown (rev_t ++ [(lr, nd, tr)]) root b p_par p_top = 
  EX p_gpar: val, EX p_sib: val, EX b_par: val, 
    !! (Int.min_signed <= key_of_node nd <= Int.max_signed) &&
    partial_treebox_rep_topdown rev_t root b_par p_gpar p_top *
    data_at Tsh (tptr t_struct_tree) p_par b_par *
    field_at Tsh t_struct_tree [StructField _color] (Vint (Int.repr (Col2Z (color_of_node nd)))) p_par *
    field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (key_of_node nd))) p_par *
    field_at Tsh t_struct_tree [StructField _value] (Vint (Int.repr (value_of_node nd))) p_par *
    field_at Tsh t_struct_tree [StructField _par] p_gpar p_par *
    rbtree_rep tr p_sib p_par *
    match lr with
    | L => !! (b = field_address t_struct_tree [StructField _right] p_par) &&
           field_at Tsh t_struct_tree [StructField _left] p_sib p_par
    | R => !! (b = field_address t_struct_tree [StructField _left] p_par) &&
           field_at Tsh t_struct_tree [StructField _right] p_sib p_par
    end.
Proof.
  revert root b p_par p_top.
  induction rev_t as [|[[LRr Ndr] Trr]]; intros.
  + apply pred_ext; simpl.
    - Intros p_ans_another_child p_ans.
      destruct lr; Exists p_top p_ans_another_child root; entailer!.
    - Intros p_gpar p_sib b_par.
      destruct lr; Exists p_sib p_par; entailer!; solve_field_compatible.
  + apply pred_ext; simpl.
    - Intros p_ans_another_child p_ans.
      destruct LRr, lr; rewrite IHrev_t;
      Intros p_gpar p_sib b_par;
      Exists p_gpar p_sib b_par p_ans_another_child p_ans; entailer!.
    - Intros p_gpar p_sib b_par p_ans_another_child p_ans.
      destruct LRr, lr;
      Exists p_ans_another_child p_ans;
      rewrite IHrev_t;
      Exists p_gpar p_sib b_par; entailer!.
Qed.

Lemma partial_treebox_rep'' (t : partial_tree) (root b p_par p_top : val):
  partial_treebox_rep t root b p_par p_top = 
  partial_treebox_rep_topdown (rev t) root b p_par p_top.
Proof.
  revert root b p_par p_top.
  induction t as [|[[LR Nd] Tr]]; intros.
  + reflexivity.
  + simpl rev.
    rewrite partial_treebox_rep_topdown_sgt.
    expand partial_treebox_rep.
    apply pred_ext; destruct LR;
    Intros p_gpar p_sib b_par; (rewrite IHt || rewrite <- IHt);
    Exists p_gpar p_sib b_par; entailer!.
Qed.

(* ----------------------------------------------------------- *)

Lemma complete':
  forall t b p_par pt root,
    treebox_rep t b p_par * partial_treebox_rep pt root b p_par nullval
    |-- treebox_rep (complete_tree pt t) root nullval.
Proof.
  intros.
  revert t b p_par root.
  induction pt; intros.
  + simpl. entailer!.
  + destruct a as [[lr n] ts].
    rewrite partial_treebox_rep'.
    Intros p_gpar p_sib b_par.
    expand complete_tree.
    destruct lr.
    - entailer!.
      pose proof treebox_rep_l p_par p_gpar p_sib ts t n b_par.
      sep_apply H14; clear H14.
      sep_apply IHpt. entailer!.
    - entailer!.
      pose proof treebox_rep_r p_par p_gpar p_sib t ts n b_par.
      sep_apply H14; clear H14.
      sep_apply IHpt. entailer!.
Qed.

Lemma complete_tree_with_T_neq_E:
  forall (l : partial_tree) (b : tree),
    b <> E -> complete_tree l b <> E.
Proof.
  intros. revert b H.
  induction l; intros.
  + tauto.
  + destruct a as [[lr n] ts].
    expand complete_tree.
    destruct lr.
    - assert((T ts n b) <> E) by apply T_neq_E.
      apply IHl, H0.
    - assert((T b n ts) <> E) by apply T_neq_E.
      apply IHl, H0.
Qed.

Lemma complete_tree_with_Part_neq_E:
  forall (l : partial_tree) (b : tree),
    l <> [] -> complete_tree l b <> E.
Proof.
  intros.
  destruct l.
  + tauto.
  + destruct h as [[lr n] ts].
    expand complete_tree.
    destruct lr.
    - assert((T ts n b) <> E) by apply T_neq_E.
      apply complete_tree_with_T_neq_E, H0.
    - assert((T b n ts) <> E) by apply T_neq_E.
      apply complete_tree_with_T_neq_E, H0.
Qed.

Lemma complete_tree_elim:
  forall l b,
    complete_tree l b = E -> b = E /\ l = [].
Proof.
  intros.
  split.
  + pose proof classic (b = E).
    destruct H0; try tauto.
    pose proof complete_tree_with_T_neq_E l b.
    tauto.
  + pose proof classic (l = []).
    destruct H0; try tauto.
    pose proof complete_tree_with_Part_neq_E l b.
    tauto.
Qed.


