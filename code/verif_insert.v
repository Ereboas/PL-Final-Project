Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import RBTree.api_spec2.
Require Import RBTree.AuxiliaryTac.
Require Import RBTree.verif_insert_balance.
Require Import Coq.Logic.Classical.
Import ListNotations.
Local Open Scope Z.

(* --------------------------------------------------------- *)
Module mallocN.
(* mallocN *)
Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [tint]
    PROP (4 <= n <= Int.max_unsigned)
    PARAMS (Vint (Int.repr n))
    GLOBALS ()
    SEP ()
  POST [ tptr tvoid ]
    EX v: val,
      PROP (malloc_compatible n v)
      RETURN (v)
      SEP (memory_block Tsh n v).
End mallocN.
(* --------------------------------------------------------- *)

Module insertFunc.
Definition insert_spec :=
 DECLARE _insert
  WITH t : tree, root : val, x : Key, v : Value
  PRE  [ tptr (tptr t_struct_tree), tint, tuint ]
    PROP (Int.min_signed <= x <= Int.max_signed) 
    PARAMS (root; Vint (Int.repr x); Vint (Int.repr v))
    SEP (treebox_rep t root nullval)
  POST [ Tvoid ]
    EX t_complete : tree, 
    PROP (insert x v t t_complete)
    RETURN ()
    SEP (treebox_rep t_complete root nullval).

Definition Gprog : funspecs :=
         ltac:(with_library prog [
             insertBalance.insert_balance_spec; mallocN.mallocN_spec; makeBlack.make_black_spec]).

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Z.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Z.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (y < x) (x >? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Z.gtb_lt.
Qed.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

(* Fixpoint num_of_node(t: tree) :=
  match t with
  | E => 0
  | T t1 n t2 => num_of_node t1 + num_of_node t2 + 1
  end.
  
Fixpoint num_of_node'(t: partial_tree) :=
  match t with
  | [] => 0
  | (_, _, t) :: l => num_of_node' l + num_of_node t + 1
  end.
  
Lemma balance'_not_change_nodenum1:
  forall l rest resl,
    balance' l E = (resl, rest) ->
    num_of_node' l = num_of_node rest + num_of_node' resl. *)

(* Lemma balance'_with_T_not_prod_E:
  forall l t resl rest,
    t <> E /\
    balance' l t = (resl, rest)->
    rest <> E. *)

Lemma body_insert: semax_body Vprog Gprog
                                    f_insert insert_spec.
Proof.
  start_function.
  assert_PROP (root<>nullval) as Hroot. { unfold treebox_rep; Intros p. entailer!. }
  forward. (* treebox root := t *)
  forward. (* struct tree* last_node := NULL *)
  forward_loop(
    EX p_last: val,
    EX b_now: val,
    EX part_now: partial_tree,
    EX t_now: tree,
      PROP (Int.min_signed <= x <= Int.max_signed;
            insert_split x t [] = insert_split x t_now part_now;
            complete_tree part_now t_now = complete_tree (@nil half_tree) t)
      LOCAL (temp _last_node p_last; temp _root root; temp _t b_now;
             temp _x (Vint (Int.repr x)); temp _value (Vint (Int.repr v)) )
      SEP (treebox_rep t_now b_now p_last;
           partial_treebox_rep part_now root b_now p_last nullval)
  )
    break:(
      EX p_last: val,
      EX p_now: val,
      EX b_now: val,
      EX part_now: partial_tree,
      EX t_before_ins: tree,
        PROP (Int.min_signed <= x <= Int.max_signed;
              complete_tree part_now t_before_ins = complete_tree (@nil half_tree) t;
             (part_now, t_before_ins) = insert_split x t [])
        LOCAL (temp _p p_now; temp _root root; temp _t b_now;
               temp _x (Vint (Int.repr x)); temp _value (Vint (Int.repr v)) )
        SEP (data_at Tsh (tptr t_struct_tree) p_now b_now;
             rbtree_rep (insert_root x v t_before_ins) p_now p_last;
             partial_treebox_rep part_now root b_now p_last nullval)).
  { Exists nullval root (@nil half_tree) t. entailer!.
    simpl. entailer!. }
  Intros p_last b_now part_now t_now.
  + simpl.
    unfold treebox_rep.
    Intros p_now.
    forward.
    forward_if_wrp.
    - forward_call (sizeof t_struct_tree).
        1: { computable. }
      Intros p_new.
      rewrite memory_block_data_at_ by auto.
      forward.
      forward.
      forward.
      forward.
      forward.
      forward.
      forward.
      forward.
      rewrite <- H1.
      Exists p_last p_new b_now part_now t_now.
      assert_PROP (t_now = E).
      { destruct t_now; expand rbtree_rep; [entailer!|].
        Intros a b. subst.
        assert_PROP False;[|contradiction].
        entailer!. }
      entailer!.
      expand insert_root.
      expand rbtree_rep.
      Exists nullval nullval; entailer!.
    - destruct t_now as [|t_l n t_r]; expand rbtree_rep.
      { assert_PROP False by entailer!; tauto. }
      Intros p_l p_r.
      forward. 
      forward_if_wrp.
      * forward.
        forward.
        Exists p_last p_now b_now part_now (T t_l n t_r).
        rewrite H0.
        expand insert_split.
        entailer!. 
        { bdestruct (key_of_node n <? key_of_node n); [lia|].
          bdestruct (key_of_node n >? key_of_node n); [lia|auto]. }
        unfold insert_root.
        expand rbtree_rep; Exists p_l p_r.
        entailer!.
      * forward.
        forward_if_wrp; forward; rewrite H0.
        ++ Exists p_now
             (field_address t_struct_tree [StructField _left] p_now) 
             ( (R, n, t_r):: part_now )
             t_l.
             entailer!.
             expand insert_split.
             { bdestruct (x <? key_of_node n); [auto|lia]. }
             expand partial_treebox_rep. unfold treebox_rep.
             Exists p_l p_last p_r b_now.
             unfold_data_at (data_at _ t_struct_tree _ p_now).
             entailer!.
        ++ Exists p_now
             (field_address t_struct_tree [StructField _right] p_now) 
             ( (L, n, t_l):: part_now )
             t_r.
             entailer!.
             expand insert_split.
             { bdestruct (x <? key_of_node n); [lia|].
               bdestruct (x >? key_of_node n); [auto|lia]. }
             expand partial_treebox_rep. unfold treebox_rep.
             Exists p_r p_last p_l b_now.
             unfold_data_at (data_at _ t_struct_tree _ p_now).
             entailer!.
  + Intros p_last p_now b_now part_now t_before_ins.
    remember (insert_root x v t_before_ins) as t_aft_ins.
    assert(insert_root x v t_before_ins <> E) by apply insert_root_neq_E.
    destruct t_aft_ins; [congruence|].
    expand rbtree_rep.
    Intros p_l p_r.
    forward.
    forward_if (
        EX l: partial_tree,
        EX s: tree,
        EX isred: bool,
        EX h: partial_tree,
        EX b: tree, 
        PROP ((l, s) = insert_split x t [];
               if isred then
                 Red_tree (insert_root x v s) /\
                 (h, b) = balance' l (insert_root x v s)
               else
                 Black_tree (insert_root x v s) )
        LOCAL (temp _root root)
        SEP (if isred then 
               treebox_rep (complete_tree h b) root nullval
             else
               treebox_rep (complete_tree l (insert_root x v s)) root nullval)
      ).
    - destruct (color_of_node n) eqn:colorN; unfold Col2Z.
      2:{ unfold Col2Z in H4; inversion H4. }
      forward_call(
        T t_aft_ins1 n t_aft_ins2,
        root, p_last, b_now, part_now ).
      { expand treebox_rep.
        Exists p_now.
        expand rbtree_rep.
        Exists p_l p_r. rewrite colorN.
        entailer!. } 
      { apply T_neq_E. }
      Intros vret.
      destruct vret as [[[t_bal part_bal] b_bal] p_par_bal].
      repeat simpl fst in * + simpl snd in *.
      Exists part_now
             t_before_ins
             true
             part_bal
             t_bal.
      entailer!.
      { rewrite <- Heqt_aft_ins.
        unfold Red_tree.
        destruct n as[nc nk nv]. assert(nc = Red)by auto.
        subst nc. tauto. }
      apply complete'.
    - destruct (color_of_node n) eqn:colorN; unfold Col2Z.
      1: { unfold Col2Z, RED_COLOR in H4. tauto. }
      forward.
      Exists part_now
             t_before_ins
             false.
      entailer!.
      pose proof treebox_rep_lr p_now p_l p_r p_last t_aft_ins1 t_aft_ins2 n b_now.
      rewrite <- Heqt_aft_ins.
      unfold Col2Z in H11.
      rewrite colorN in H11.
      unfold Black_tree.
      destruct n as[nc nk nv]. assert(nc = Black)by auto.
      subst nc. remember {| color_of_node := Black; key_of_node := nk; value_of_node := nv |} as n.
      sep_apply H11; clear H11.
      entailer.
      apply complete'.
    - Intros l s isred h b.
      rewrite <- H1 in H4.
      injection H4 as ? ?; subst.
      destruct isred eqn:Ered.
      2:{ forward_call(
            complete_tree part_now (insert_root x v t_before_ins),
            root, nullval).
          Exists (makeBlack (complete_tree part_now (insert_root x v t_before_ins))).
          entailer!.
          apply insert_intro_Black.
          { apply H1. }
          { apply H5. }
      }
      destruct H5.
      forward_call(
            complete_tree h b,
            root, nullval).
      Exists (makeBlack (complete_tree h b)).
          entailer!.
          eapply insert_intro_Red.
          { apply H1. }
          { apply H4. }
          { apply H5. }
Qed.
End insertFunc.