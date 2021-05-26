Require Import VST.floyd.proofauto.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import RBTree.AuxiliaryTac.
Require Import RBTree.api_spec2.
Require Import Coq.Logic.Classical.
Import ListNotations.
Local Open Scope Z.


Module insertBalance.
Definition insert_balance_spec :=
  DECLARE _insert_balance
  WITH t_initial: tree, 
       root: val,
       p_par_initial: val,
       b_initial: val, 
       ls_initial: partial_tree
  PRE [ tptr (tptr t_struct_tree), 
        tptr (tptr t_struct_tree) ]
    PROP (t_initial <> E)
    PARAMS (b_initial; root) 
    SEP (treebox_rep t_initial b_initial p_par_initial; 
         partial_treebox_rep ls_initial root b_initial 
           p_par_initial nullval) (* 应当清楚: partial_treebox_rep 记录了以b为根的树的补集的所有值&一阶指针信息, 以及b的二级指针 *)
  POST [ Tvoid ]
    EX t_balanced: tree, 
    EX ls_balanced: partial_tree, 
    EX b_balanced: val, 
    EX p_par_balanced: val,
    PROP ((ls_balanced, t_balanced) = balance' ls_initial t_initial)
    RETURN ()
    SEP (treebox_rep t_balanced b_balanced p_par_balanced; 
         partial_treebox_rep ls_balanced root b_balanced 
           p_par_balanced nullval).

Definition Gprog : funspecs :=
         ltac:(with_library prog [
           makeBlack.make_black_spec; getColor1.get_color1_spec; getColor2.get_color2_spec;
             leftRotate.left_rotate_spec; leftRotateWrap.left_rotate_wrap_spec;
             rightRotate.right_rotate_spec; rightRotateWrap.right_rotate_wrap_spec;
             insert_balance_spec ]).

Lemma body_insert_balance: semax_body Vprog Gprog
                                    f_insert_balance insert_balance_spec.
Proof.
  start_function.
  unfold treebox_rep.
  Intros p_initial.
  destruct t_initial eqn:t_init_fact; [congruence|].
  (* T t1 n t2 <> E *)
  expand rbtree_rep.
  Intros p_init_l p_init_r.
  forward. (* struct tree * p = *t *)
  forward_loop (
    EX t_med: tree,
    EX ls_med: partial_tree,
    EX b_med: val,
    EX p_par_med: val,
    EX p_med: val,
      PROP ( t_initial <> E; p_med <> nullval; (*^*)
             balance' ls_med t_med = balance' ls_initial t_initial )
      LOCAL (temp _p p_med;(*  temp _t b_med; *) temp _root root)
      SEP ( data_at Tsh (tptr t_struct_tree) p_med b_med;
            rbtree_rep t_med p_med p_par_med;
            partial_treebox_rep ls_med root b_med 
              p_par_med nullval)
  ).
  + (* 前条件满足不变量 *)
    Exists t_initial ls_initial b_initial p_par_initial p_initial.
    entailer!.
    expand rbtree_rep.
    Exists p_init_l p_init_r.
    entailer!.
  + Intros tree_med ls_med b_med p_par_med p_med. (* 这些带有"med"的变量是循环不变量处<即此处>引入的, 用以和后续引入的变量区分 *)
    destruct tree_med as [|lch node_med rch] eqn:Etree_med.
    ++ (* tree_med = [] => p_med=nullval. 与^矛盾*)
       expand rbtree_rep.
       assert_PROP False by entailer!.
       contradiction.
    ++ (* "tree_med =  T lch node_med rch" => p_med<>nullval 保证了"p_med有非空子树" *)
       expand rbtree_rep.
       Intros p_lch p_rch.
       forward.  (* p_par = p->par; *)
       destruct ls_med eqn:Els_med.
       - (* ls_med = [] => p_par_med = nullval *) (* "没有父亲 => 矛盾" *)
         expand partial_treebox_rep.
         assert_PROP (p_par_med = nullval) by entailer!.
         assert_PROP (b_med = root) by entailer!.
         forward_call(p_par_med, nullval, p_lch, p_rch, node_med, false). (* calculate get_color1(p_par) *)
         { entailer!. }
         tauto.
         forward_if. (* if (get_color(p_par) != RED) *)
         -- (* get_color(p_par) != RED *)
            forward.
            Exists (T lch node_med rch) (@nil half_tree) root nullval.
            entailer!.
            unfold partial_treebox_rep, treebox_rep.
            Exists p_med.
            entailer!.
            expand rbtree_rep.
            Exists p_lch p_rch.
            entailer!.
         -- (* get_color(p_par) = RED => contradiction *)
            assert_PROP False by entailer!.
            contradiction.
       - (* "ls_med = h :: p" *) (* "有父亲节点" *)
         destruct h as [[L_or_R node_par] Tree_Lsib_Or_Rsib] eqn:Ehalf_par.
         destruct L_or_R.
         rename p into part_par.
         * (* "ls_med = (L, node_par, tree_lsib) :: part_par" *) (* """p为右子树""" *)
           rename Tree_Lsib_Or_Rsib into tree_lsib.
           remember (T tree_lsib node_par tree_med) as tree_par.
           expand partial_treebox_rep.
           Intros p_gpar p_lsib b_par.
           assert_PROP (p_par_med <> nullval) by entailer!. (* "p_par_med <> nullval" *)
           forward_call(p_par_med, p_gpar, p_lsib, p_med, node_par, true). (* get_color1(p_par) *)
           { entailer!. (* 满足前条件 *)
             entailer!.
             unfold_data_at (data_at _ t_struct_tree _ p_par_med).
             entailer!. }
           { split; congruence. }
           destruct (color_of_node node_par) eqn:Ecolor_par.
           2: { (* color_par = Black *) (* "父亲的颜色是黑色, 情况平凡" *)
                unfold Col2Z at 1 2.
                forward_if; (* if (get_color(p_par) != RED) *)
                   [|assert_PROP False by entailer!; contradiction].
                forward.  (* return *)
                Exists (T lch node_med rch) 
                       ((L, node_par, tree_lsib) :: part_par)
                       (field_address t_struct_tree [StructField _right] p_par_med)
                       p_par_med.
                expand treebox_rep.
                expand partial_treebox_rep.
                Exists p_med p_gpar p_lsib b_par.
                expand rbtree_rep.
                Exists p_lch p_rch.
                entailer!.
                { rewrite <- H3.
                  expand balance'.
                  rewrite Ecolor_par.
                  destruct part_par; [auto|].
                  destruct h as [[? ?] ?]; auto. }
                unfold_data_at (data_at Tsh t_struct_tree _ p_par_med).
                entailer!.
                rewrite Ecolor_par.
                unfold Col2Z.
                entailer!.
               }
           ** (* "Ecolor_par : color_of_node node_par = Red" *) (* "父亲的颜色是红色" *)
              unfold Col2Z at 1 2.
              forward_if. (* if (get_color(p_par) != RED) *)
              { congruence. } (* get_color(p_par) != RED => contradiction *)
              forward. (* p_gpar = p_par->par; *)
              destruct part_par eqn:Epart_par.
              *** (* part_par = [] => p_gpar = p_top = nullval *) (* "没有祖父节点, 情况平凡" *)
                  expand partial_treebox_rep.
                  assert_PROP (p_gpar = nullval) by entailer!.
                  assert_PROP (b_par = root) by entailer!. 
                  forward_if. (* if (p_gpar == NULL) *)
                  2: { congruence. }
                  forward. (* p_gpar = NULL; return! *)
                  rewrite <- H3.
                  Exists (T lch node_med rch)
                         [(L, node_par, tree_lsib)]
                         (field_address t_struct_tree [StructField _right] p_par_med)
                         p_par_med. 
                  entailer!.
                  expand treebox_rep.
                  Exists p_med.
                  expand partial_treebox_rep.
                  Exists nullval p_lsib b_par.
                  expand rbtree_rep.
                  Exists p_lch p_rch.
                  unfold_data_at (data_at _ t_struct_tree _ p_par_med).
                  rewrite Ecolor_par.
                  entailer!.
              *** (* part_par = h0 :: l => p_gpar <> nullval *) (* "有祖父节点" *)
                  destruct h0 as [[L_or_R node_gpar] Tree_Lunc_Or_Runc] eqn:Ehalf_gpar.
                  destruct L_or_R.
                  rename l into part_gpar.
                  +++ (* part_par = (L, node_gpar, Tree_Lunc_Or_Runc) :: part_gpar *) (* """p_par为右子树""" *)
                      rename Tree_Lunc_Or_Runc into tree_lunc.
                      remember (T tree_lunc node_gpar tree_par) as tree_gpar.
                        (* tree_gpar = T tree_lunc node_gpar tree_par *)
                      expand partial_treebox_rep.
                      Intros p_ggpar p_lunc b_gpar.
                      assert_PROP (p_gpar <> nullval) by entailer!. (* "p_gpar <> nullval" *)
                      gather_SEP 5 7 8 9 10 11.
                      replace_SEP 0 (
                        data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node node_gpar))),
                                                   (Vint (Int.repr (key_of_node node_gpar)),
                                                    (Vint (Int.repr (value_of_node node_gpar)),
                                                     (p_lunc, (p_par_med, p_ggpar))))) p_gpar
                      ).
                      { entailer!.
                        unfold_data_at (data_at _ t_struct_tree _ p_gpar).
                        entailer!. }
                      forward_if. (* if (p_gpar == NULL) *)
                      { congruence. }
                      forward. (* calculate p_gpar->left *)
                      forward_if_wrp. (* if (p_par == p_gpar->left) *)
                      --- (* p_par == p_gpar->left => p_par = p_lunc => contradiction! *)
                          destruct tree_lunc as [|tree_lunc_l node_lunc tree_lunc_r] eqn:ETree_lunc.
                          { expand rbtree_rep.
                            assert_PROP False by entailer!.
                            contradiction. }
                          { expand rbtree_rep. (* tree_lunc = T tree_lunc_l node_lunc tree_lunc_r *)
                            Intros p_lunc_l p_lunc_r.
                            assert_PROP False.
                            { focus_SEP 1. (* 调换位置 *)
                              sep_apply data_at_conflict; auto.
                              entailer!. }
                            contradiction. }
                      --- (* "p_par == p_gpar->right" *)
                          forward. (* calculate p_gpar->left *)
                          
                          destruct tree_lunc as [|tree_lunc_l node_lunc tree_lunc_r] eqn:ETree_lunc.
                          ++++ (* "tree_lunc = E" *)
                               expand rbtree_rep.
                               assert_PROP (p_lunc = nullval) by entailer!.
                               
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *)                            
                               
                               forward_call( (* get_color2(p_gpar->left) *)
                                 tree_lunc, p_lunc, p_gpar, false
                               ). 
                               { entailer!. } (* 满足前条件 *)
                               { tauto. }
                               forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                               { contradiction. }
                               forward. (* p_gpar->color = RED; *)
                               forward. (* cal p_gpar->right *)
                               forward_if_wrp. (* if (p == p_par->left) *)
                               **** (* p = p_par->left => p = p_lisb => contradiction *)
                                    destruct tree_lsib as [|tree_lsib_l node_lsib tree_lsib_r] eqn:ETree_lsib.
                                    { expand rbtree_rep.
                                      assert_PROP False by entailer!.
                                      contradiction. }
                                    { expand rbtree_rep.
                                        Intros p_lunc_l p_lunc_r.
                                        assert_PROP False. 
                                        { focus_SEP 3. (* 调换位置 *)
                                          sep_apply data_at_conflict; auto.
                                          entailer!. }
                                        contradiction. }
                               **** (* "p = p_par->right" *)
                                    forward. (* p_par->color = BLACK; *)
                                    destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                    +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                          expand partial_treebox_rep.
                                          assert_PROP (p_ggpar = nullval) by entailer!.
                                          assert_PROP (b_gpar = root) by entailer!.
                                          (* call: left_rotate_wrap(p_gpar, root) *)
                                          forward_call(
                                            p_gpar, p_par_med, p_ggpar, p_lsib,
                                            p_lunc, p_med, p_gpar, nullval, 
                                            RedNode node_gpar, BlackNode node_par,
                                            tree_lunc, tree_med, tree_lsib,
                                            root, false,
                                            false, nullval, nullval, node_par, (* 此行无用 *)
                                            true, E (* 此行无用 *)
                                          ).
                                          { entailer!. (* 满足前条件 *)
                                            expand partial_tree_rep.
                                            expand rbtree_rep.
                                            Exists p_lch p_rch.
                                            entailer!. }
                                          { repeat split; try tauto; (* 满足前条件 *)
                                            subst; auto. }
                                          forward.
                                          remember (T lch node_med rch) as tree_med.
                                          Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                    (BlackNode node_par)
                                                    tree_med) 
                                                 (@nil half_tree)
                                                 root nullval.
                                          rewrite <- H3.
                                          expand balance'.
                                          rewrite Ecolor_par.
                                          unfold l_rotate.
                                          expand rbtree_rep.
                                          expand partial_treebox_rep.
                                          entailer!.
                                          expand treebox_rep.
                                          Exists p_par_med.
                                          entailer!.
                                          remember (T lch node_med rch) as tree_med.
                                          expand rbtree_rep.
                                          Exists p_gpar p_med nullval p_lsib.
                                          entailer!.
                                    +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                          destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                          assert_PROP (p_ggpar <> nullval). {
                                            destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                          destruct LR; expand partial_treebox_rep;
                                          Intros p_gggpar p_ggpl_or_r b_ggpar;
                                          assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                          assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                            rename p_ggpl_or_r into p_ggpl.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpl <> p_gpar).
                                              destruct H25.
                                              destruct H26. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; simpl.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpl <> p_gpar *)
                                              destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                     p_gpar, p_par_med, p_ggpar, p_lsib,
                                                     p_lunc, p_med, p_ggpar, nullval, 
                                                     RedNode node_gpar, BlackNode node_par,
                                                     tree_lunc, tree_med, tree_lsib,
                                                     root, true,
                                                     false, p_gggpar, p_ggpl, node_ggpar,
                                                     true, E).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                rewrite <- H3.
                                                Exists (T (T E (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                       [(L, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer.
                                                remember (T lch node_med rch) as tree_med.
                                                expand rbtree_rep.
                                                Exists p_gpar p_med nullval p_lsib.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                     p_gpar, p_par_med, p_ggpar, p_lsib,
                                                     p_lunc, p_med, p_ggpar, nullval, 
                                                     RedNode node_gpar, BlackNode node_par,
                                                     tree_lunc, tree_med, tree_lsib,
                                                     root, true,
                                                     false, p_gggpar, p_ggpl, node_ggpar,
                                                     false, tree_ggpl).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                rewrite <- H3.
                                                Exists (T (T E (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                       [(L, node_ggpar, tree_ggpl)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpl b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                expand rbtree_rep.
                                                Exists p_gpar p_med nullval p_lsib.
                                                entailer!.
                                              }  
                                          (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpl <> p_gpar).
                                              destruct H24. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; simpl.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                            }
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpr.
                                            rename p_ggpl_or_r into p_ggpr.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpr <> p_gpar).
                                              destruct H25.
                                              destruct H26. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; simpl.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpr <> p_gpar *)
                                              destruct tree_ggpr as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                     p_gpar, p_par_med, p_ggpar, p_lsib,
                                                     p_lunc, p_med, p_ggpar, nullval, 
                                                     RedNode node_gpar, BlackNode node_par,
                                                     tree_lunc, tree_med, tree_lsib,
                                                     root, true,
                                                     true, p_gggpar, p_ggpr, node_ggpar,
                                                     true, E).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                rewrite <- H3.
                                                Exists (T (T E (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                       [(R, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer.
                                                remember (T lch node_med rch) as tree_med.
                                                expand rbtree_rep.
                                                Exists p_gpar p_med nullval p_lsib.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                     p_gpar, p_par_med, p_ggpar, p_lsib,
                                                     p_lunc, p_med, p_ggpar, nullval, 
                                                     RedNode node_gpar, BlackNode node_par,
                                                     tree_lunc, tree_med, tree_lsib,
                                                     root, true,
                                                     true, p_gggpar, p_ggpr, node_ggpar,
                                                     false, tree_ggpr).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                rewrite <- H3.
                                                Exists (T (T E (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                       [(R, node_ggpar, tree_ggpr)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpr b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                expand rbtree_rep.
                                                Exists p_gpar p_med nullval p_lsib.
                                                entailer!.
                                              }  
                                          (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpr <> p_gpar).
                                              destruct H24. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; simpl.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T E (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med nullval p_lsib.
                                                  entailer!.
                                              }
                          ++++ (* "tree_lunc = T tree_lunc_l node_lunc tree_lunc_r" *)
                               assert_PROP (p_lunc <> nullval).
                               { expand rbtree_rep; Intros a b; entailer!. }
                               destruct (color_of_node node_lunc) eqn: color_lunc.
                               ---- (* "lunc is RED" *)
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *) 
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_lunc, p_lunc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite ETree_lunc, color_lunc.
                                 unfold Col2Z at 1. (*  , RED_COLOR, BLACK_COLOR. *)
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 2: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 expand rbtree_rep.
                                 Intros p_lunc_l p_lunc_r.
                                 forward.
                                 forward.
                                 forward.
                                 Exists (T (makeBlack tree_lunc) (RedNode node_gpar)
                                         (T tree_lsib (BlackNode node_par) tree_med))
                                   part_gpar
                                   b_gpar
                                   p_ggpar
                                   p_gpar.
                                 rewrite <- H3.
                                 expand balance'.
                                 rewrite Ecolor_par.
                                 expand rbtree_rep.
                                 Exists p_lunc p_par_med p_lsib p_med.
                                 entailer!.
                                 2:{ unfold makeBlack. expand rbtree_rep. 
                                     Exists p_lunc_l p_lunc_r p_lch p_rch.
                                     entailer!. } 
                                 simpl (color_of_node node_lunc).
                                 destruct node_lunc as [a b c].
                                 assert(a = Red).
                                 { auto. }
                                 subst. reflexivity.
                               ---- (* "lunc is BLACK" *)
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_lunc, p_lunc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite ETree_lunc, color_lunc.
                                 unfold Col2Z at 1, RED_COLOR, BLACK_COLOR.
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 1: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 forward_if_wrp. (* if (p == p_par->left) *)
                                 **** (* p = p_par->left => p = p_lisb => contradiction *)
                                   destruct tree_lsib as [|tree_lsib_l node_lsib tree_lsib_r] eqn:ETree_lsib.
                                   { expand rbtree_rep.
                                     assert_PROP False by entailer!.
                                     contradiction. }
                                   { expand rbtree_rep.
                                     Intros p_lunc_l p_lunc_r p_lsib_l p_lsib_r.
                                     assert_PROP False. 
                                     { focus_SEP 8. (* 调换位置 *)
                                       sep_apply data_at_conflict; auto.
                                       entailer!. }
                                     contradiction. }
                                 **** (* "p = p_par->right" *)
                                   forward. (* p_par->color = BLACK; *)
                                   destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                   +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                     expand partial_treebox_rep.
                                     assert_PROP (p_ggpar = nullval) by entailer!.
                                     assert_PROP (b_gpar = root) by entailer!.
                                     (* call: left_rotate_wrap(p_gpar, root) *)
                                     forward_call(
                                     p_gpar, p_par_med, p_ggpar, p_lsib,
                                     p_lunc, p_med, p_gpar, nullval, 
                                     RedNode node_gpar, BlackNode node_par,
                                     tree_lunc, tree_med, tree_lsib,
                                     root, false,
                                     false, nullval, nullval, node_par, (* 此行无用 *)
                                     true, E (* 此行无用 *)
                                     ).
                                     { entailer!. (* 满足前条件 *)
                                       expand partial_tree_rep.
                                       expand rbtree_rep.
                                       Exists p_lch p_rch.
                                       entailer!. }
                                     { repeat split; try tauto; (* 满足前条件 *)
                                       subst; auto. }
                                     forward.
                                     remember (T lch node_med rch) as tree_med.
                                     Exists 
                                       (T 
                                         (T 
                                           (T tree_lunc_l node_lunc tree_lunc_r) 
                                           (RedNode node_gpar) tree_lsib)
                                         (BlackNode node_par)
                                         tree_med)
                                               (@nil half_tree)
                                               root nullval.
                                     rewrite <- H3.
                                     expand balance'.
                                     rewrite Ecolor_par.
                                     destruct node_lunc as[c_lunc k_lunc v_lunc].
                                     assert(c_lunc = Black)by auto.
                                     subst c_lunc.
                                     unfold l_rotate.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                     expand partial_treebox_rep.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                     expand treebox_rep.
                                     Exists p_par_med.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                     remember (T lch node_med rch) as tree_med.
                                     expand rbtree_rep.
                                     Intros p_lunc_l p_lunc_r.
                                     Exists p_gpar p_med p_lunc p_lsib p_lunc_l p_lunc_r.
                                     entailer!.
                                   +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                     destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                     assert_PROP (p_ggpar <> nullval).
                                     { destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                     destruct LR; expand partial_treebox_rep;
                                       Intros p_gggpar p_ggpl_or_r b_ggpar;
                                       assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                       assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                     -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                       rename p_ggpl_or_r into p_ggpl.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpl <> p_gpar).
                                       destruct H25.
                                       destruct H26. 
                                       2:{ assert(p_ggpl = p_gpar) by tauto.
                                           destruct tree_ggpl; simpl.
                                           { assert_PROP (p_ggpl = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b c d. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 3.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpl <> p_gpar *)
                                       destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                       *****
                                         rewrite <- ETree_lunc.
                                         expand rbtree_rep.
                                         forward_call(
                                           p_gpar, p_par_med, p_ggpar, p_lsib,
                                           p_lunc, p_med, p_ggpar, nullval, 
                                           RedNode node_gpar, BlackNode node_par,
                                           tree_lunc, tree_med, tree_lsib,
                                           root, true,
                                           false, p_gggpar, p_ggpl, node_ggpar,
                                           true, E).
                                         { entailer!. expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                         rewrite <- H3.
                                         Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                  [(L, node_ggpar, E)]
                                                  (field_address t_struct_tree [StructField _right] p_ggpar)
                                                  p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         remember (T lch node_med rch) as tree_med.
                                         expand rbtree_rep. Intros a b.
                                         Exists p_gpar p_med p_lunc p_lsib a b.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         rewrite <- ETree_lunc.
                                         forward_call(
                                           p_gpar, p_par_med, p_ggpar, p_lsib,
                                           p_lunc, p_med, p_ggpar, nullval, 
                                           RedNode node_gpar, BlackNode node_par,
                                           tree_lunc, tree_med, tree_lsib,
                                           root, true,
                                           false, p_gggpar, p_ggpl, node_ggpar,
                                           false, tree_ggpl).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpl.
                                           expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                         rewrite <- H3.
                                         Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                [(L, node_ggpar, tree_ggpl)]
                                                (field_address t_struct_tree [StructField _right] p_ggpar)
                                                p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpl b_ggpar. entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer!.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                         remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                         expand rbtree_rep.
                                         Exists p_gpar p_med p_lunc p_lsib.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpl <> p_gpar).
                                         destruct H24. 
                                         2:{ assert(p_ggpl = p_gpar) by tauto.
                                             destruct tree_ggpl; expand rbtree_rep.
                                             { assert_PROP (p_ggpl = nullval) by entailer!.
                                               subst. congruence. }
                                             Intros a b c d. subst.
                                             assert_PROP False;[|contradiction].
                                             focus_SEP 3.
                                             sep_apply data_at_conflict;auto.
                                             entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         *****
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_gpar p_med p_lunc p_lsib a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med p_lunc p_lsib.
                                                  entailer!.
                                             *****
                                               Intros p_ans_another_child p_ans.
                                               destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_gpar p_med p_lunc p_lsib a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med p_lunc p_lsib.
                                                  entailer!.
                                                  }
                                       -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                       rename p_ggpl_or_r into p_ggpl.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpl <> p_gpar).
                                       destruct H25.
                                       destruct H26. 
                                       2:{ assert(p_ggpl = p_gpar) by tauto.
                                           destruct tree_ggpl; simpl.
                                           { assert_PROP (p_ggpl = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b c d. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 3.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpl <> p_gpar *)
                                       destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                       *****
                                         rewrite <- ETree_lunc.
                                         expand rbtree_rep.
                                         forward_call(
                                           p_gpar, p_par_med, p_ggpar, p_lsib,
                                           p_lunc, p_med, p_ggpar, nullval, 
                                           RedNode node_gpar, BlackNode node_par,
                                           tree_lunc, tree_med, tree_lsib,
                                           root, true,
                                           true, p_gggpar, p_ggpl, node_ggpar,
                                           true, E).
                                         { entailer!. expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                         rewrite <- H3.
                                         Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                  [(R, node_ggpar, E)]
                                                  (field_address t_struct_tree [StructField _left] p_ggpar)
                                                  p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         remember (T lch node_med rch) as tree_med.
                                         expand rbtree_rep. Intros a b.
                                         Exists p_gpar p_med p_lunc p_lsib a b.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         rewrite <- ETree_lunc.
                                         forward_call(
                                           p_gpar, p_par_med, p_ggpar, p_lsib,
                                           p_lunc, p_med, p_ggpar, nullval, 
                                           RedNode node_gpar, BlackNode node_par,
                                           tree_lunc, tree_med, tree_lsib,
                                           root, true,
                                           true, p_gggpar, p_ggpl, node_ggpar,
                                           false, tree_ggpl).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpl.
                                           expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                         rewrite <- H3.
                                         Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib) (BlackNode node_par) tree_med)
                                                [(R, node_ggpar, tree_ggpl)]
                                                (field_address t_struct_tree [StructField _left] p_ggpar)
                                                p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpl b_ggpar. entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer!.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                         remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                         expand rbtree_rep.
                                         Exists p_gpar p_med p_lunc p_lsib.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpl <> p_gpar).
                                         destruct H24. 
                                         2:{ assert(p_ggpl = p_gpar) by tauto.
                                             destruct tree_ggpl; expand rbtree_rep.
                                             { assert_PROP (p_ggpl = nullval) by entailer!.
                                               subst. congruence. }
                                             Intros a b c d. subst.
                                             assert_PROP False;[|contradiction].
                                             focus_SEP 3.
                                             sep_apply data_at_conflict;auto.
                                             entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         *****
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_gpar p_med p_lunc p_lsib a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med p_lunc p_lsib.
                                                  entailer!.
                                             *****
                                               Intros p_ans_another_child p_ans.
                                               destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_gpar p_med p_lunc p_lsib a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_par_med, p_ggpar, p_lsib,
                                                       p_lunc, p_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_par,
                                                       tree_lunc, tree_med, tree_lsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lunc (RedNode node_gpar) tree_lsib)
                                                          (BlackNode node_par)
                                                          tree_med) 
                                                       ((R, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) 
                                                      as node_lunc +
                                                    remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_med p_lunc p_lsib.
                                                  entailer!. }
                  +++ (* Epart_par : part_par = (R, node_gpar, Tree_Lunc_Or_Runc) :: l *)
                      rename l into part_gpar.
                      rename Tree_Lunc_Or_Runc into tree_runc.
                      remember (T tree_runc node_gpar tree_par) as tree_gpar.
                        (* tree_gpar = T tree_runc node_gpar tree_par *)
                      expand partial_treebox_rep.
                      Intros p_ggpar p_runc b_gpar.
                      assert_PROP (p_gpar <> nullval) by entailer!. (* "p_gpar <> nullval" *)
                      assert_PROP (is_pointer_or_null p_gpar) by entailer!.
                      gather_SEP 5 7 8 9 10 11.
                      replace_SEP 0 (
                        data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node node_gpar))),
                                                   (Vint (Int.repr (key_of_node node_gpar)),
                                                    (Vint (Int.repr (value_of_node node_gpar)),
                                                     (p_par_med, (p_runc, p_ggpar))))) p_gpar
                      ).
                      { entailer!.
                        unfold_data_at (data_at _ t_struct_tree _ p_gpar).
                        entailer!. }
                      forward_if. (* if (p_gpar == NULL) *)
                      { congruence. }
                      forward. (* calculate p_gpar->left *)
                      forward_if_wrp. (* if (p_par == p_gpar->left) *)
                      (* "p_par == p_gpar->left" *)
                          forward. (* calculate p_gpar->right *)
                          destruct tree_runc as [|tree_runc_l node_runc tree_runc_r] eqn:Etree_runc.
                          ++++ (* "tree_runc = E" *)
                               expand rbtree_rep.
                               assert_PROP (p_runc = nullval) by entailer!.
                               
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *)                            
                               
                               forward_call( (* get_color2(p_gpar->left) *)
                                 tree_runc, p_runc, p_gpar, false
                               ). 
                               { entailer!. } (* 满足前条件 *)
                               { tauto. }
                               forward_if. (* if (get_color2(p_gpar->right) == RED) *)
                               { contradiction. }
                               forward. (* p_gpar->color = RED; *)
                               forward. (* cal p_gpar->right *)
                               forward_if_wrp. (* if (p == p_par->right) *)
                               (* "p = p_par->right" *)
                                    forward. (* p->color = BLACK; *)
                                    forward_call(
                                      p_par_med, p_med, p_gpar, p_lch, p_lsib, p_rch,
                                      node_par, BlackNode node_med,
                                      tree_lsib, rch, lch
                                    ).
                                    { rewrite Ecolor_par.
                                      unfold Col2Z at 1.
                                      entailer!. }
                                    forward.
                                    destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                    +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                          expand partial_treebox_rep.
                                          assert_PROP (p_ggpar = nullval) by entailer!.
                                          assert_PROP (b_gpar = root) by entailer!.
                                          (* call: right_rotate_wrap(p_gpar, root) *)
                                          forward_call(
                                            p_med, p_gpar, p_ggpar, p_rch,
                                            p_par_med, p_runc, p_gpar, nullval, 
                                            BlackNode node_med, RedNode node_gpar,
                                            T tree_lsib node_par lch, tree_runc, rch,
                                            root, false,
                                            false, nullval, nullval, node_par, (* 此行无用 *)
                                            true, E (* 此行无用 *)
                                          ).
                                          { entailer!. (* 满足前条件 *)
                                            expand partial_tree_rep.
                                            expand rbtree_rep.
                                            Exists p_lsib p_lch.
                                            entailer!. }
                                          { repeat split; try tauto; (* 满足前条件 *)
                                            subst; auto. }
                                          forward.
                                          remember (T tree_lsib node_par lch) as tree_par_new.
                                          Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) E))
                                                 (@nil half_tree)
                                                 root nullval.
                                          rewrite <- H3.
                                          expand balance'.
                                          rewrite Ecolor_par.
                                          unfold l_rotate, r_rotate, makeBlack.
                                          expand rbtree_rep.
                                          expand partial_treebox_rep.
                                          entailer!.
                                          expand treebox_rep.
                                          Exists p_med.
                                          remember (T tree_lsib node_par lch) as tree_par_new.
                                          expand rbtree_rep.
                                          Exists p_par_med p_gpar p_rch nullval.
                                          entailer!.
                                    +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                          destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                          assert_PROP (p_ggpar <> nullval). {
                                            destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                          destruct LR; expand partial_treebox_rep;
                                          Intros p_gggpar p_ggpl_or_r b_ggpar;
                                          assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                          assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                            rename p_ggpl_or_r into p_ggpl.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpl <> p_gpar).
                                              destruct H27.
                                              destruct H28. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; simpl.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpl <> p_gpar *)
                                              destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lsib p_lch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                rewrite <- H3.
                                                Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) E))
                                                       [(L, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                expand rbtree_rep.
                                                Exists p_par_med p_gpar p_rch nullval.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  false, tree_ggpl
                                                ).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  Exists p_lsib p_lch; entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                rewrite <- H3.
                                                Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) E))
                                                       [(L, node_ggpar, tree_ggpl)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpl b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                expand rbtree_rep.
                                                Exists p_par_med p_gpar p_rch nullval.
                                                entailer!.
                                              }  
                                          (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpl <> p_gpar).
                                              destruct H26. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; expand rbtree_rep.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) E))
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) E))
                                                         ((L, node_ggpar, tree_ggpl) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) E))
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) E))
                                                         ((L, node_ggpar, tree_ggpl) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                            }
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpr.
                                            rename p_ggpl_or_r into p_ggpr.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpr <> p_gpar).
                                              destruct H27.
                                              destruct H28. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; simpl.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpr <> p_gpar *)
                                              destruct tree_ggpr as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lsib p_lch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                rewrite <- H3.
                                                Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) E))
                                                       [(R, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                expand rbtree_rep.
                                                Exists p_par_med p_gpar p_rch nullval.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  false, tree_ggpr
                                                ).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  Exists p_lsib p_lch; entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                rewrite <- H3.
                                                Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) E))
                                                       [(R, node_ggpar, tree_ggpr)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpr b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T tree_lsib node_par lch) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                expand rbtree_rep.
                                                Exists p_par_med p_gpar p_rch nullval.
                                                entailer!.
                                              }  
                                          (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpr <> p_gpar).
                                              destruct H26. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; expand rbtree_rep.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) E))
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) E))
                                                         ((R, node_ggpar, tree_ggpr) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) E))
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) E))
                                                         ((R, node_ggpar, tree_ggpr) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T tree_lsib node_par lch) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch nullval.
                                                  entailer!.
                                            }
                          ++++ (* "tree_runc = T tree_runc_l node_runc tree_runc_r" *)
                               assert_PROP (p_runc <> nullval).
                               { expand rbtree_rep; Intros a b; entailer!. }
                               destruct (color_of_node node_runc) eqn: color_runc.
                               ---- (* "lunc is RED" *)
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *) 
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_runc, p_runc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite Etree_runc, color_runc.
                                 unfold Col2Z at 1. (*  , RED_COLOR, BLACK_COLOR. *)
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 2: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 expand rbtree_rep.
                                 Intros p_runc_l p_runc_r.
                                 forward.
                                 forward.
                                 forward.
                                 Exists (T 
                                   (T tree_lsib (BlackNode node_par) tree_med) (RedNode node_gpar)
                                   (makeBlack tree_runc))
                                   part_gpar
                                   b_gpar
                                   p_ggpar
                                   p_gpar.
                                 rewrite <- H3.
                                 expand balance'.
                                 rewrite Ecolor_par.
                                 expand rbtree_rep.
                                 Exists p_par_med p_runc p_lsib p_med.
                                 entailer!.
                                 2:{ unfold makeBlack. expand rbtree_rep. 
                                     Exists p_lch p_rch p_runc_l p_runc_r.
                                     entailer!. } 
                                 simpl (color_of_node node_runc).
                                 destruct node_runc as [a b c].
                                 assert(a = Red).
                                 { auto. }
                                 subst. reflexivity.
                               ---- (* "lunc is BLACK" *)
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_runc, p_runc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite Etree_runc, color_runc.
                                 unfold Col2Z at 1, RED_COLOR, BLACK_COLOR.
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 1: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 forward_if_wrp.
                                 (* "p = p_par->right" *)
                                   forward. (* p_par->color = BLACK; *)
                                   forward_call(
                                      p_par_med, p_med, p_gpar, p_lch, p_lsib, p_rch,
                                      node_par, BlackNode node_med,
                                      tree_lsib, rch, lch
                                    ).
                                    { rewrite Ecolor_par.
                                      unfold Col2Z at 1.
                                      entailer!. }
                                    forward.
                                   destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                   +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                     expand partial_treebox_rep.
                                     assert_PROP (p_ggpar = nullval) by entailer!.
                                     assert_PROP (b_gpar = root) by entailer!.
                                     (* call: left_rotate_wrap(p_gpar, root) *)
                                     forward_call(
                                            p_med, p_gpar, p_ggpar, p_rch,
                                            p_par_med, p_runc, p_gpar, nullval, 
                                            BlackNode node_med, RedNode node_gpar,
                                            T tree_lsib node_par lch, tree_runc, rch,
                                            root, false,
                                            false, nullval, nullval, node_par, (* 此行无用 *)
                                            true, E (* 此行无用 *)
                                          ).
                                          { entailer!. (* 满足前条件 *)
                                            expand partial_tree_rep.
                                            expand rbtree_rep.
                                            Exists p_lsib p_lch.
                                            entailer!. }
                                          { repeat split; try tauto; (* 满足前条件 *)
                                            subst; auto. }
                                          forward.
                                     remember (T tree_lsib node_par lch) as tree_par_new.
                                     remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                     Exists 
                                       (T 
                                         (T tree_lsib node_par lch) (BlackNode node_med)
                                           (T rch (RedNode node_gpar)
                                        tree_runc))
                                       (@nil half_tree)
                                       root nullval.
                                     rewrite <- H3.
                                     expand balance'.
                                     rewrite Ecolor_par.
                                     destruct node_runc as[c_lunc k_lunc v_lunc].
                                     assert(c_lunc = Black)by auto.
                                     subst c_lunc tree_runc.
                                     unfold l_rotate, r_rotate, makeBlack.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc.
                                     expand partial_treebox_rep.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc.
                                     expand treebox_rep.
                                     Exists p_med.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc.
                                     remember (T tree_lsib node_par lch) as tree_par_new.
                                     remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                     expand rbtree_rep.
                                     Exists p_par_med p_gpar p_rch p_runc.
                                     entailer!.
                                   +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                     destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                     assert_PROP (p_ggpar <> nullval).
                                     { destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                     destruct LR; expand partial_treebox_rep;
                                       Intros p_gggpar p_ggpl_or_r b_ggpar;
                                       assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                       assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                     -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                       rename p_ggpl_or_r into p_ggpl.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpl <> p_gpar).
                                       destruct H27.
                                       destruct H28. 
                                       2:{ assert(p_ggpl = p_gpar) by tauto.
                                           destruct tree_ggpl; simpl.
                                           { assert_PROP (p_ggpl = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 8.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpl <> p_gpar *)
                                       destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                       *****
                                         expand rbtree_rep.
                                         forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lsib p_lch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         rewrite <- H3.
                                         Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) tree_runc))
                                                       [(L, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_runc.
                                         destruct node_runc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         expand rbtree_rep.
                                         Exists p_par_med p_gpar p_rch p_runc.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  false, tree_ggpl
                                                ).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpl.
                                           expand rbtree_rep.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           Exists p_lsib p_lch; entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         rewrite <- H3.
                                         Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) tree_runc))
                                                       [(L, node_ggpar, tree_ggpl)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_runc.
                                         destruct node_runc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpl b_ggpar.
                                         entailer!.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         expand rbtree_rep.
                                         Exists p_par_med p_gpar p_rch p_runc.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpl <> p_gpar).
                                         destruct H26. 
                                         2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; expand rbtree_rep.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 8.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         ++++++
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) tree_runc))
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) tree_runc))
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                           ++++++
                                               Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) tree_runc))
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) tree_runc))
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                                  }
                                       -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpr.
                                       rename p_ggpl_or_r into p_ggpr.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpr <> p_gpar).
                                       destruct H27.
                                       destruct H28. 
                                       2:{ assert(p_ggpr = p_gpar) by tauto.
                                           destruct tree_ggpr; simpl.
                                           { assert_PROP (p_ggpr = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 8.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpr <> p_gpar *)
                                       destruct tree_ggpr as[|? ? ?] eqn:Tree.
                                       *****
                                         expand rbtree_rep.
                                         forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lsib p_lch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         rewrite <- H3.
                                         Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) tree_runc))
                                                       [(R, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_runc.
                                         destruct node_runc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         expand rbtree_rep.
                                         Exists p_par_med p_gpar p_rch p_runc.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         forward_call(
                                                  p_med, p_gpar, p_ggpar, p_rch,
                                                  p_par_med, p_runc, p_ggpar, nullval, 
                                                  BlackNode node_med, RedNode node_gpar,
                                                  T tree_lsib node_par lch, tree_runc, rch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  false, tree_ggpr
                                                ).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpr.
                                           expand rbtree_rep.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           Exists p_lsib p_lch; entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         rewrite <- H3.
                                         Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                   (T rch (RedNode node_gpar) tree_runc))
                                                       [(R, node_ggpar, tree_ggpr)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_runc.
                                         destruct node_runc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpr b_ggpar.
                                         entailer!.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         expand rbtree_rep.
                                         Exists p_par_med p_gpar p_rch p_runc.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpr <> p_gpar).
                                         destruct H26. 
                                         2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; expand rbtree_rep.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 8.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         ++++++
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) tree_runc))
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) tree_runc))
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                           ++++++
                                               Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                         (T rch (RedNode node_gpar) tree_runc))
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_med, p_gpar, p_ggpar, p_rch,
                                                       p_par_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_med, RedNode node_gpar,
                                                       T tree_lsib node_par lch, tree_runc, rch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lsib p_lch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T (T tree_lsib node_par lch) (BlackNode node_med)
                                                           (T rch (RedNode node_gpar) tree_runc))
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_runc +
									  remember (T tree_lsib node_par lch) as tree_par_new +
									  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_par_med p_gpar p_rch p_runc.
                                                  entailer!.
                                                  }
* (* Els_med : ls_med = (R, node_par, Tree_Lsib_Or_Rsib) :: p *) (* "p为左子树" *)
  rename Tree_Lsib_Or_Rsib into tree_rsib.
  rename p into part_par.
  remember (T tree_med node_par tree_rsib) as tree_par.
  expand partial_treebox_rep.
  Intros p_gpar p_rsib b_par.
  assert_PROP (p_par_med <> nullval) by entailer!.
  forward_call(p_par_med, p_gpar, p_med, p_rsib, node_par, true). (* get_color1(p_par) *)
  { entailer!. (* 满足前条件 *)
    unfold_data_at (data_at _ t_struct_tree _ p_par_med).
    entailer!. }
  { split; congruence. }
  destruct (color_of_node node_par) eqn:Ecolor_par.
  2: { (* color_par = Black *) (* "父亲的颜色是黑色, 情况平凡" *)
                unfold Col2Z at 1 2.
                forward_if; (* if (get_color(p_par) != RED) *)
                   [|assert_PROP False by entailer!; contradiction].
                forward.  (* return *)
                Exists (T lch node_med rch) 
                       ((R, node_par, tree_rsib) :: part_par)
                       (field_address t_struct_tree [StructField _left] p_par_med)
                       p_par_med.
                expand treebox_rep.
                expand partial_treebox_rep.
                Exists p_med p_gpar p_rsib b_par.
                expand rbtree_rep.
                Exists p_lch p_rch.
                entailer!.
                { rewrite <- H3.
                  expand balance'.
                  rewrite Ecolor_par.
                  destruct part_par; [auto|].
                  destruct h as [[? ?] ?]; auto. }
                unfold_data_at (data_at Tsh t_struct_tree _ p_par_med).
                entailer!.
                rewrite Ecolor_par.
                unfold Col2Z.
                entailer!.
     }
  ** (* "Ecolor_par : color_of_node node_par = Red" *) (* "父亲的颜色是红色" *)
              unfold Col2Z at 1 2.
              forward_if. (* if (get_color(p_par) != RED) *)
              { congruence. } (* get_color(p_par) != RED => contradiction *)
              forward. (* p_gpar = p_par->par; *)
  destruct part_par eqn:Epart_par.
   *** (* part_par = [] => p_gpar = p_top = nullval *) (* "没有祖父节点, 情况平凡" *)
                  expand partial_treebox_rep.
                  assert_PROP (p_gpar = nullval) by entailer!.
                  assert_PROP (b_par = root) by entailer!. 
                  forward_if. (* if (p_gpar == NULL) *)
                  2: { congruence. }
                  forward. (* p_gpar = NULL; return! *)
                  rewrite <- H3.
                  Exists (T lch node_med rch) 
                         [(R, node_par, tree_rsib)]
                         (field_address t_struct_tree [StructField _left] p_par_med)
                          p_par_med.
                  entailer!.
                  expand treebox_rep.
                  Exists p_med.
                  expand partial_treebox_rep.
                  Exists nullval p_rsib b_par.
                  expand rbtree_rep.
                  Exists p_lch p_rch.
                  unfold_data_at (data_at _ t_struct_tree _ p_par_med).
                  rewrite Ecolor_par.
                  entailer!.
   *** (* part_par = h0 :: l => p_gpar <> nullval *) (* "有祖父节点" *)
                  destruct h0 as [[L_or_R node_gpar] Tree_Lunc_Or_Runc] eqn:Ehalf_gpar.
                  destruct L_or_R.
                  rename l into part_gpar.
                  +++ (* part_par = (L, node_gpar, Tree_Lunc_Or_Runc) :: part_gpar *) (* """p_par为右子树""" *)
                      rename Tree_Lunc_Or_Runc into tree_lunc.
                      remember (T tree_lunc node_gpar tree_par) as tree_gpar.
                        (* tree_gpar = T tree_lunc node_gpar tree_par *)
                      expand partial_treebox_rep.
                      Intros p_ggpar p_lunc b_gpar.
                      assert_PROP (p_gpar <> nullval) by entailer!. (* "p_gpar <> nullval" *)
                      assert_PROP (is_pointer_or_null p_gpar) by entailer!.
                      gather_SEP 5 7 8 9 10 11.
                      replace_SEP 0 (
                        data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node node_gpar))),
                                                   (Vint (Int.repr (key_of_node node_gpar)),
                                                    (Vint (Int.repr (value_of_node node_gpar)),
                                                     (p_lunc, (p_par_med, p_ggpar))))) p_gpar
                      ).
                      { entailer!.
                        unfold_data_at (data_at _ t_struct_tree _ p_gpar).
                        entailer!. }
                     forward_if. (* if (p_gpar == NULL) *)
                      { congruence. }
                      forward. (* calculate p_gpar->left *)
                      forward_if_wrp. (* if (p_par == p_gpar->left) *) 
                     --- (* p_par == p_gpar->left => p_par = p_lunc => contradiction! *)
                          destruct tree_lunc as [|tree_lunc_l node_lunc tree_lunc_r] eqn:ETree_lunc.
                          { expand rbtree_rep.
                            assert_PROP False by entailer!.
                            contradiction. }
                          { expand rbtree_rep. (* tree_lunc = T tree_lunc_l node_lunc tree_lunc_r *)
                            Intros p_lunc_l p_lunc_r.
                            assert_PROP False.
                            { focus_SEP 1. (* 调换位置 *)
                              sep_apply data_at_conflict; auto.
                              entailer!. }
                            contradiction. }
                     --- (* "p_par == p_gpar->right" *)
                          forward. (* calculate p_gpar->left *)
                          destruct tree_lunc as [|tree_lunc_l node_lunc tree_lunc_r] eqn:ETree_lunc.
                          ++++ (* "tree_lunc = E" *)
                               expand rbtree_rep.
                               assert_PROP (p_lunc = nullval) by entailer!.
                               
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *)                            
                               
                               forward_call( (* get_color2(p_gpar->left) *)
                                 tree_lunc, p_lunc, p_gpar, false
                               ). 
                               { entailer!. } (* 满足前条件 *)
                               { tauto. }
                               forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                               { contradiction. }
                               forward. (* p_gpar->color = RED; *)
                               forward. (* cal p_gpar->right *)
                               forward_if_wrp. (* if (p == p_par->left) *)
                               (*" p = p_par->left "*)
                                    forward. (* p->color = BLACK; *)
                                    forward_call(
                                      p_med, p_par_med, p_gpar, p_rch, p_lch, p_rsib,
                                      BlackNode node_med, node_par,
                                       lch, tree_rsib, rch
                                    ).
                                    { rewrite Ecolor_par.
                                      unfold Col2Z at 1.
                                      entailer!. }
                                    forward.
                                    destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                    +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                          expand partial_treebox_rep.
                                          assert_PROP (p_ggpar = nullval) by entailer!.
                                          assert_PROP (b_gpar = root) by entailer!.
                                          (* call: left_rotate_wrap(p_gpar, root) *)
                                          forward_call(
                                            p_gpar, p_med, p_ggpar, p_lch,
                                            p_lunc, p_par_med, p_gpar, nullval, 
                                            RedNode node_gpar, BlackNode node_med,
                                            tree_lunc, T rch node_par tree_rsib, lch,
                                            root, false,
                                            false, nullval, nullval, node_par, (* 此行无用 *)
                                            true, E (* 此行无用 *)
                                          ).
                                          { entailer!. (* 满足前条件 *)
                                            expand partial_tree_rep.
                                            expand rbtree_rep.
                                            Exists p_rch p_rsib.
                                            entailer!. }
                                          { repeat split; try tauto; (* 满足前条件 *)
                                            subst; auto. }
                                          forward.
                                          remember (T rch node_par tree_rsib) as tree_par_new.
                                          Exists (T 
                                                   (T E (RedNode node_gpar) lch) 
                                                   (BlackNode node_med) 
                                                   tree_par_new)
                                                 (@nil half_tree)
                                                 root nullval.
                                          rewrite <- H3.
                                          expand balance'.
                                          rewrite Ecolor_par.
                                          unfold l_rotate, r_rotate, makeBlack.
                                          expand rbtree_rep.
                                          expand partial_treebox_rep.
                                          entailer!.
                                          expand treebox_rep.
                                          Exists p_med.
                                          remember (T rch node_par tree_rsib) as tree_par_new.
                                          expand rbtree_rep.
                                          Exists p_gpar p_par_med nullval p_lch.
                                          entailer!.
                                    +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                          destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                          assert_PROP (p_ggpar <> nullval). {
                                            destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                          destruct LR; expand partial_treebox_rep;
                                          Intros p_gggpar p_ggpl_or_r b_ggpar;
                                          assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                          assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                            rename p_ggpl_or_r into p_ggpl.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpl <> p_gpar).
                                              destruct H27.
                                              destruct H28. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; simpl.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpl <> p_gpar *)
                                              destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_rch p_rsib; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                rewrite <- H3.
                                                Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(L, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                expand rbtree_rep.
                                                Exists p_gpar p_par_med nullval p_lch.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  false, tree_ggpl
                                                ).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  Exists p_rch p_rsib; entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                rewrite <- H3.
                                                Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(L, node_ggpar, tree_ggpl)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpl b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                expand rbtree_rep.
                                                Exists p_gpar p_par_med nullval p_lch.
                                                entailer!.
                                              }
                                              (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpl <> p_gpar).
                                              destruct H26. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; expand rbtree_rep.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                              ------
                                                assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ans, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((L, node_ggpar, tree_ggpl) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ans, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ans, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((L, node_ggpar, tree_ggpl) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                            }
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpr.
                                            rename p_ggpl_or_r into p_ggpr.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpr <> p_gpar).
                                              destruct H27.
                                              destruct H28. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; simpl.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpr <> p_gpar *)
                                              destruct tree_ggpr as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_rch p_rsib; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                rewrite <- H3.
                                                Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(R, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                expand rbtree_rep.
                                                Exists p_gpar p_par_med nullval p_lch.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  false, tree_ggpr
                                                ).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  Exists p_rch p_rsib; entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                rewrite <- H3.
                                                Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(R, node_ggpar, tree_ggpr)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold l_rotate, r_rotate, makeBlack.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpr b_ggpar.
                                                expand treebox_rep.
                                                Exists p_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T rch node_par tree_rsib) as tree_par_new.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                expand rbtree_rep.
                                                Exists p_gpar p_par_med nullval p_lch.
                                                entailer!.
                                              }  
                                              (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpr <> p_gpar).
                                              destruct H26. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; expand rbtree_rep.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 5.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((R, node_ggpar, tree_ggpr) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  rewrite <- Heqtree_par_new.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T 
                                                         (T E (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((R, node_ggpar, tree_ggpr) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T rch node_par tree_rsib) as tree_par_new.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med nullval p_lch.
                                                  entailer!.
                                            }
                            ++++ (* "tree_lunc = T tree_lunc_l node_lunc tree_lunc_r" *)
                               assert_PROP (p_lunc <> nullval).
                               { expand rbtree_rep; Intros a b; entailer!. }
                               destruct (color_of_node node_lunc) eqn: color_lunc.
                               ---- (* "lunc is RED" *)
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *) 
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_lunc, p_lunc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite ETree_lunc, color_lunc.
                                 unfold Col2Z at 1. (*  , RED_COLOR, BLACK_COLOR. *)
                                 forward_if. (* if (get_color2(p_gpar->right) == RED) *)
                                 2: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 expand rbtree_rep.
                                 Intros p_lunc_l p_lunc_r.
                                 forward.
                                 forward.
                                 forward.
                                 Exists (T (makeBlack tree_lunc) 
                                           (RedNode node_gpar)
                                           (T tree_med (BlackNode node_par) tree_rsib))
                                   part_gpar
                                   b_gpar
                                   p_ggpar
                                   p_gpar.
                                 rewrite <- H3.
                                 expand balance'.
                                 rewrite Ecolor_par.
                                 expand rbtree_rep.
                                 Exists p_lunc p_par_med p_med p_rsib.
                                 entailer!.
                                 2:{ unfold makeBlack. expand rbtree_rep. 
                                     Exists p_lunc_l p_lunc_r p_lch p_rch.
                                     entailer!. } 
                                 simpl (color_of_node node_lunc).
                                 destruct node_lunc as [a b c].
                                 assert(a = Red).
                                 { auto. }
                                 subst. reflexivity.
                               ---- (* "lunc is BLACK" *)
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_lunc, p_lunc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite ETree_lunc, color_lunc.
                                 unfold Col2Z at 1, RED_COLOR, BLACK_COLOR.
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 1: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 forward_if_wrp.
                                 (* "p = p_par->left" *)
                                   forward. (* p_par->color = BLACK; *)
                                   forward_call(
                                      p_med, p_par_med, p_gpar, p_rch, p_lch, p_rsib,
                                      BlackNode node_med, node_par,
                                       lch, tree_rsib, rch
                                    ).
                                    { rewrite Ecolor_par.
                                      unfold Col2Z at 1.
                                      entailer!. }
                                    forward.
                                   destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                   +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                     expand partial_treebox_rep.
                                     assert_PROP (p_ggpar = nullval) by entailer!.
                                     assert_PROP (b_gpar = root) by entailer!.
                                     (* call: left_rotate_wrap(p_gpar, root) *)
                                     forward_call(
                                            p_gpar, p_med, p_ggpar, p_lch,
                                            p_lunc, p_par_med, p_gpar, nullval, 
                                            RedNode node_gpar, BlackNode node_med,
                                            tree_lunc, T rch node_par tree_rsib, lch,
                                            root, false,
                                            false, nullval, nullval, node_par, (* 此行无用 *)
                                            true, E (* 此行无用 *)
                                          ).
                                          { entailer!. (* 满足前条件 *)
                                            expand partial_tree_rep.
                                            expand rbtree_rep.
                                            Exists p_rch p_rsib.
                                            entailer!. }
                                          { repeat split; try tauto; (* 满足前条件 *)
                                            subst; auto. }
                                          forward.
                                     remember (T rch node_par tree_rsib) as tree_par_new.
                                     remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                     Exists 
                                       (T 
                                                   (T tree_lunc (RedNode node_gpar) lch) 
                                                   (BlackNode node_med) 
                                                   tree_par_new)
                                       (@nil half_tree)
                                       root nullval.
                                     rewrite <- H3.
                                     expand balance'.
                                     rewrite Ecolor_par.
                                     destruct node_lunc as[c_lunc k_lunc v_lunc].
                                     assert(c_lunc = Black)by auto.
                                     subst c_lunc tree_lunc.
                                     unfold l_rotate, r_rotate, makeBlack.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                     expand partial_treebox_rep.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                     expand treebox_rep.
                                     Exists p_med.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc.
                                     remember (T rch node_par tree_rsib) as tree_par_new.
                                     remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc.
                                     expand rbtree_rep.
                                     Exists p_gpar p_par_med p_lunc p_lch.
                                     entailer!.
                                   +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                     destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                     assert_PROP (p_ggpar <> nullval).
                                     { destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                     destruct LR; expand partial_treebox_rep;
                                       Intros p_gggpar p_ggpl_or_r b_ggpar;
                                       assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                       assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                     -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                       rename p_ggpl_or_r into p_ggpl.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpl <> p_gpar).
                                       destruct H27.
                                       destruct H28. 
                                       2:{ assert(p_ggpl = p_gpar) by tauto.
                                           destruct tree_ggpl; simpl.
                                           { assert_PROP (p_ggpl = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 8.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpl <> p_gpar *)
                                       destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                       *****
                                         expand rbtree_rep.
                                         forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_rch p_rsib; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         rewrite <- H3.
                                         Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(L, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         expand rbtree_rep.
                                         Exists p_gpar p_par_med p_lunc p_lch.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  false, p_gggpar, p_ggpl, node_ggpar,
                                                  false, tree_ggpl
                                                ).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpl.
                                           expand rbtree_rep.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           Exists p_rch p_rsib; entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         rewrite <- H3.
                                         Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(L, node_ggpar, tree_ggpl)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpl b_ggpar.
                                         entailer!.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         expand rbtree_rep.
                                         Exists p_gpar p_par_med p_lunc p_lch.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpl <> p_gpar).
                                         destruct H26. 
                                         2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; expand rbtree_rep.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 8.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         ++++++
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                           ++++++
                                               Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((L, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _right] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                                  }
                                       -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpr.
                                       rename p_ggpl_or_r into p_ggpr.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpr <> p_gpar).
                                       destruct H27.
                                       destruct H28. 
                                       2:{ assert(p_ggpr = p_gpar) by tauto.
                                           destruct tree_ggpr; simpl.
                                           { assert_PROP (p_ggpr = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 8.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpr <> p_gpar *)
                                       destruct tree_ggpr as[|? ? ?] eqn:Tree.
                                       *****
                                         expand rbtree_rep.
                                         forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  true, E
                                                ).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_rch p_rsib; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         rewrite <- H3.
                                         Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(R, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         expand rbtree_rep.
                                         Exists p_gpar p_par_med p_lunc p_lch.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         forward_call(
                                                  p_gpar, p_med, p_ggpar, p_lch,
                                                  p_lunc, p_par_med, p_ggpar, nullval, 
                                                  RedNode node_gpar, BlackNode node_med,
                                                  tree_lunc, T rch node_par tree_rsib, lch,
                                                  root, true,
                                                  true, p_gggpar, p_ggpr, node_ggpar,
                                                  false, tree_ggpr
                                                ).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpr.
                                           expand rbtree_rep.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           Exists p_rch p_rsib; entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         rewrite <- H3.
                                         Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       [(R, node_ggpar, tree_ggpr)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_lunc.
                                         destruct node_lunc as[c_lunc k_lunc v_lunc].
                                         assert(c_lunc = Black)by auto.
                                         subst c_lunc.
                                         unfold l_rotate, r_rotate, makeBlack.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpr b_ggpar.
                                         entailer!.
                                         repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                         expand treebox_rep.
                                         Exists p_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         expand rbtree_rep.
                                         Exists p_gpar p_par_med p_lunc p_lch.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpr <> p_gpar).
                                         destruct H26. 
                                         2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; expand rbtree_rep.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 8.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         ++++++
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                           ++++++
                                               Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                         ((R, node_ggpar, E) :: l)
                                                         (field_address t_struct_tree [StructField _left] p_ggpar)
                                                         p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_gpar, p_med, p_ggpar, p_lch,
                                                       p_lunc, p_par_med, p_ans, nullval, 
                                                       RedNode node_gpar, BlackNode node_med,
                                                       tree_lunc, T rch node_par tree_rsib, lch,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_rch p_rsib; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T 
                                                         (T tree_lunc (RedNode node_gpar) lch) 
                                                         (BlackNode node_med) 
                                                         tree_par_new)
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_lunc.
                                                  destruct node_lunc as[c_lunc k_lunc v_lunc].
                                                  assert(c_lunc = Black)by auto.
                                                  subst c_lunc. repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  unfold l_rotate, r_rotate, makeBlack.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat
									  remember ({| color_of_node := Black; key_of_node := k_lunc; value_of_node := v_lunc |}) as node_lunc +
									  remember (T rch node_par tree_rsib) as tree_par_new +
									  remember (T tree_lunc_l node_lunc tree_lunc_r) as tree_lunc +
									  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_gpar p_par_med p_lunc p_lch.
                                                  entailer!.
                                                  }
+++ rename l into part_gpar. (* part_par = (R, node_gpar, Tree_Lunc_Or_Runc) :: part_gpar *)
    rename Tree_Lunc_Or_Runc into tree_runc.
                      remember (T tree_runc node_gpar tree_par) as tree_gpar.
                        (* tree_gpar = T tree_lunc node_gpar tree_par *)
                      expand partial_treebox_rep.
                      Intros p_ggpar p_runc b_gpar.
                      assert_PROP (p_gpar <> nullval) by entailer!. (* "p_gpar <> nullval" *)
                      gather_SEP 5 7 8 9 10 11.
                      replace_SEP 0 (
                        data_at Tsh t_struct_tree (Vint (Int.repr (Col2Z (color_of_node node_gpar))),
                                                   (Vint (Int.repr (key_of_node node_gpar)),
                                                    (Vint (Int.repr (value_of_node node_gpar)),
                                                     (p_par_med, (p_runc, p_ggpar))))) p_gpar
                      ).
                      { entailer!.
                        unfold_data_at (data_at _ t_struct_tree _ p_gpar).
                        entailer!. }
                      forward_if. (* if (p_gpar == NULL) *)
                      { congruence. }
                      forward. (* calculate p_gpar->left *)
                      forward_if_wrp. (* "p_par == p_gpar->left" *)
                      forward. (* calculate p_gpar->left *)
                          destruct tree_runc as [|tree_runc_l node_runc tree_runc_r] eqn:ETree_runc.
                          ++++ (* "tree_runc = E" *)
                               expand rbtree_rep.
                               assert_PROP (p_runc = nullval) by entailer!.
                               
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *)                            
                               
                               forward_call( (* get_color2(p_gpar->left) *)
                                 tree_runc, p_runc, p_gpar, false
                               ). 
                               { entailer!. } (* 满足前条件 *)
                               { tauto. }
                               forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                               { contradiction. }
                               forward. (* p_gpar->color = RED; *)
                               forward. (* cal p_par->right *)
                               forward_if_wrp. (* if (p == p_par->right) *)
                          **** (* p = p_par->right => p = p_rsib => contradiction *)
                                    destruct tree_rsib as [|tree_rsib_l node_rsib tree_rsib_r] eqn:ETree_rsib.
                                    { expand rbtree_rep.
                                      assert_PROP False by entailer!.
                                      contradiction. }
                                    { expand rbtree_rep.
                                        Intros p_runc_l p_runc_r.
                                        assert_PROP False. 
                                        { focus_SEP 3. (* 调换位置 *)
                                          sep_apply data_at_conflict; auto.
                                          entailer!. }
                                        contradiction. }
                         **** (* "p = p_par->right" *)
                                    forward. (* p_par->color = BLACK; *)
                                    destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                    +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                          expand partial_treebox_rep.
                                          assert_PROP (p_ggpar = nullval) by entailer!.
                                          assert_PROP (b_gpar = root) by entailer!.
                                          (* call: right_rotate_wrap(p_gpar, root) *)
                                          forward_call(
                                            p_par_med, p_gpar, p_ggpar, p_rsib,
                                            p_med, p_runc, p_gpar, nullval, 
                                            BlackNode node_par, RedNode node_gpar,
                                            tree_med, tree_runc, tree_rsib,
                                            root, false,
                                            false, nullval, nullval, node_par, (* 此行无用 *)
                                            true, E (* 此行无用 *)
                                          ).
                                          { entailer!. (* 满足前条件 *)
                                            expand partial_tree_rep.
                                            expand rbtree_rep.
                                            Exists p_lch p_rch.
                                            entailer!. }
                                          { repeat split; try tauto; (* 满足前条件 *)
                                            subst; auto. }
                                          forward.
                                          remember (T lch node_med rch) as tree_med.
                                          Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                 (@nil half_tree)
                                                 root nullval.
                                          rewrite <- H3.
                                          expand balance'.
                                          rewrite Ecolor_par.
                                          unfold r_rotate.
                                          expand rbtree_rep.
                                          expand partial_treebox_rep.
                                          entailer!.
                                          expand treebox_rep.
                                          Exists p_par_med.
                                          entailer!.
                                          remember (T lch node_med rch) as tree_med.
                                          expand rbtree_rep.
                                          Exists p_med p_gpar p_rsib nullval.
                                          entailer!.
                                        +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                          destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                          assert_PROP (p_ggpar <> nullval). {
                                            destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                          destruct LR; expand partial_treebox_rep;
                                          Intros p_gggpar p_ggpl_or_r b_ggpar;
                                          assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                          assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                            rename p_ggpl_or_r into p_ggpl.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpl <> p_gpar).
                                              destruct H25.
                                              destruct H26. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; simpl.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpl <> p_gpar *)
                                              destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                     p_par_med, p_gpar, p_ggpar, p_rsib,
                                                     p_med, p_runc, p_ggpar, nullval, 
                                                     BlackNode node_par, RedNode node_gpar,
                                                     tree_med, tree_runc, tree_rsib,
                                                     root, true,
                                                     false, p_gggpar, p_ggpl, node_ggpar,
                                                     true, E).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                rewrite <- H3.
                                                Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       [(L, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold r_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer.
                                                remember (T lch node_med rch) as tree_med.
                                                expand rbtree_rep.
                                                Exists p_med p_gpar p_rsib nullval.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                     p_par_med, p_gpar, p_ggpar, p_rsib,
                                                     p_med, p_runc, p_ggpar, nullval, 
                                                     BlackNode node_par, RedNode node_gpar,
                                                     tree_med, tree_runc, tree_rsib,
                                                     root, true,
                                                     false, p_gggpar, p_ggpl, node_ggpar,
                                                     false, tree_ggpl).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                rewrite <- H3.
                                                Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       [(L, node_ggpar, tree_ggpl)]
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold r_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpl b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpl.
                                                expand rbtree_rep.
                                                Exists p_med p_gpar p_rsib nullval.
                                                entailer!.
                                              }  
                                          (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpl <> p_gpar).
                                              destruct H24. 
                                              2:{ assert(p_ggpl = p_gpar) by tauto.
                                                  destruct tree_ggpl; simpl.
                                                  { assert_PROP (p_ggpl = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                            }
                                          ----
                                            rename Tree_ggpl_Or_ggpr into tree_ggpr.
                                            rename p_ggpl_or_r into p_ggpr.
                                            rewrite partial_treebox_rep''.
                                            destruct (rev l) eqn:El.
                                            (* El : rev l = [] *)
                                            { assert (l = [])by (apply rev_nil_elim in El; auto).
                                              assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                              { expand partial_treebox_rep_topdown. entailer!. }
                                              expand partial_treebox_rep_topdown.
                                              pose proof classic (p_ggpr <> p_gpar).
                                              destruct H25.
                                              destruct H26. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; simpl.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              (* p_ggpr <> p_gpar *)
                                              destruct tree_ggpr as[|? ? ?] eqn:Tree.
                                              -----
                                                expand rbtree_rep.
                                                forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ggpar, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                     root, true,
                                                     true, p_gggpar, p_ggpr, node_ggpar,
                                                     true, E).
                                                { entailer!. expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                rewrite <- H3.
                                                Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       [(R, node_ggpar, E)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold r_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval nullval b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer.
                                                remember (T lch node_med rch) as tree_med.
                                                expand rbtree_rep.
                                                Exists p_med p_gpar p_rsib nullval.
                                                entailer!.
                                              -----
                                                rewrite <- Tree.
                                                forward_call(
                                                     p_par_med, p_gpar, p_ggpar, p_rsib,
                                                     p_med, p_runc, p_ggpar, nullval, 
                                                     BlackNode node_par, RedNode node_gpar,
                                                     tree_med, tree_runc, tree_rsib,
                                                     root, true,
                                                     true, p_gggpar, p_ggpr, node_ggpar,
                                                     false, tree_ggpr).
                                                { entailer!. 
                                                  remember ((T t3 n0 t4)) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_lch p_rch; entailer!.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!. }
                                                { repeat split; try tauto; subst; auto. intros. congruence. }
                                                forward.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                rewrite <- H3.
                                                Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       [(R, node_ggpar, tree_ggpr)]
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                expand balance'.
                                                rewrite Ecolor_par.
                                                unfold r_rotate.
                                                expand rbtree_rep.
                                                expand partial_treebox_rep.
                                                Exists nullval p_ggpr b_ggpar.
                                                expand treebox_rep.
                                                Exists p_par_med.
                                                unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                entailer!.
                                                remember (T lch node_med rch) as tree_med.
                                                remember (T t3 n0 t4) as tree_ggpr.
                                                expand rbtree_rep.
                                                Exists p_med p_gpar p_rsib nullval.
                                                entailer!.
                                              }  
                                          (* El : rev l = h2 :: l0 *)
                                            { pose proof classic (p_ggpr <> p_gpar).
                                              destruct H24. 
                                              2:{ assert(p_ggpr = p_gpar) by tauto.
                                                  destruct tree_ggpr; simpl.
                                                  { assert_PROP (p_ggpr = nullval) by entailer!.
                                                    subst. congruence. }
                                                  Intros a b. subst.
                                                  assert_PROP False;[|contradiction].
                                                  focus_SEP 1.
                                                  sep_apply data_at_conflict;auto.
                                                  entailer!. }
                                              destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                              expand partial_treebox_rep_topdown.
                                              destruct LR_ans. 
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                              -----
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpr as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpr = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                                ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpr, node_ggpar,
                                                       false, tree_ggpr).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  Exists (T tree_med (BlackNode node_par) 
                                                   (T tree_rsib (RedNode node_gpar) E))
                                                       ((R, node_ggpar, tree_ggpr) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par.
                                                  unfold r_rotate.
                                                  expand rbtree_rep.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpr b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  remember (T lch node_med rch) as tree_med.
                                                  remember (T t3 n0 t4) as tree_ggpr.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib nullval.
                                                  entailer!.
                                              }
              ++++ (* "tree_runc = T tree_runc_l node_runc tree_runc_r" *)
                               assert_PROP (p_runc <> nullval).
                               { expand rbtree_rep; Intros a b; entailer!. }
                               destruct (color_of_node node_runc) eqn: color_runc.
                               ---- (* "runc is RED" *)
(* DECLARE _get_color2
  WITH t: tree,
       p: val,
       p_par: val,
       b: bool *)
  (* (b = false <-> p = nullval)  *) 
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_runc, p_runc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite ETree_runc, color_runc.
                                 unfold Col2Z at 1. (*  , RED_COLOR, BLACK_COLOR. *)
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 2: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 expand rbtree_rep.
                                 Intros p_runc_l p_runc_r.
                                 forward.
                                 forward.
                                 forward.
                                 Exists (T (T tree_med (BlackNode node_par) tree_rsib)
                                        (RedNode node_gpar) (makeBlack tree_runc))
                                   part_gpar
                                   b_gpar
                                   p_ggpar
                                   p_gpar.
                                 rewrite <- H3.
                                 expand balance'.
                                 rewrite Ecolor_par.
                                 expand rbtree_rep.
                                 Exists p_par_med p_runc p_med p_rsib.
                                 entailer!.
                                 2:{ unfold makeBlack. expand rbtree_rep. 
                                     Exists p_lch p_rch p_runc_l p_runc_r.
                                     entailer!. } 
                                 simpl (color_of_node node_runc).
                                 destruct node_runc as [a b c].
                                 assert(a = Red).
                                 { auto. }
                                 subst. reflexivity.
                               ---- (* "lunc is BLACK" *)
                                 forward_call( (* get_color2(p_gpar->left) *)
                                   tree_runc, p_runc, p_gpar, true
                                 ). 
                                 { entailer!. } (* 满足前条件 *)
                                 { tauto. }
                                 rewrite ETree_runc, color_runc.
                                 unfold Col2Z at 1, RED_COLOR, BLACK_COLOR.
                                 forward_if. (* if (get_color2(p_gpar->left) == RED) *)
                                 1: { assert_PROP False by entailer!; tauto. }
                                 forward.
                                 forward.
                                 forward_if_wrp. (* if (p == p_par->right) *)
                                 **** (* p = p_par->right => p = p_risb => contradiction *)
                                   destruct tree_rsib as [|tree_rsib_l node_rsib tree_rsib_r] eqn:ETree_lsib.
                                   { expand rbtree_rep.
                                     assert_PROP False by entailer!.
                                     contradiction. }
                                   { expand rbtree_rep.
                                     Intros p_runc_l p_runc_r p_rsib_l p_rsib_r.
                                     assert_PROP False. 
                                     { focus_SEP 8. (* 调换位置 *)
                                       sep_apply data_at_conflict; auto.
                                       entailer!. }
                                     contradiction. }
                                 **** (* "p = p_par->right" *)
                                   forward. (* p_par->color = BLACK; *)
                                   destruct part_gpar eqn:Egpart_par. (* 讨论gpar是否有父亲 目的是确定根节点是不是gpar *)
                                   +++++ (* part_gpar = [] *) (* gpar 是根节点 *)
                                     expand partial_treebox_rep.
                                     assert_PROP (p_ggpar = nullval) by entailer!.
                                     assert_PROP (b_gpar = root) by entailer!.
                                     (* call: right_rotate_wrap(p_gpar, root) *)
                                     forward_call(
                                     p_par_med, p_gpar, p_ggpar, p_rsib,
                                     p_med, p_runc, p_gpar, nullval, 
                                     BlackNode node_par, RedNode node_gpar,
                                     tree_med, tree_runc, tree_rsib,
                                     root, false,
                                     false, nullval, nullval, node_par, (* 此行无用 *)
                                     true, E (* 此行无用 *)
                                     ).
                                     { entailer!. (* 满足前条件 *)
                                       expand partial_tree_rep.
                                       expand rbtree_rep.
                                       Exists p_lch p_rch.
                                       entailer!. }
                                     { repeat split; try tauto; (* 满足前条件 *)
                                       subst; auto. }
                                     forward.
                                     remember (T lch node_med rch) as tree_med.
                                     Exists 
                                     (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r)))
                                               (@nil half_tree)
                                               root nullval.
                                     rewrite <- H3.
                                     expand balance'.
                                     rewrite Ecolor_par.
                                     destruct node_runc as[c_runc k_runc v_runc].
                                     assert(c_runc = Black)by auto.
                                     subst c_runc.
                                     unfold r_rotate.
                                     remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) as node_runc.
                                     expand partial_treebox_rep.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) as node_runc.
                                     expand treebox_rep.
                                     Exists p_par_med.
                                     entailer!.
                                     remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) as node_runc.
                                     remember (T lch node_med rch) as tree_med.
                                     expand rbtree_rep.
                                     Intros p_runc_l p_runc_r.
                                     Exists p_med p_gpar p_rsib p_runc p_runc_l p_runc_r.
                                     entailer!.
                                   +++++ (* part_gpar = h1 :: l *) (* gpar 不是根节点 *)
                                     destruct h1 as [[LR node_ggpar] Tree_ggpl_Or_ggpr] eqn:Ehalf_ggpar.
                                     assert_PROP (p_ggpar <> nullval).
                                     { destruct LR; expand partial_treebox_rep; Intros a b c; entailer!. }
                                     destruct LR; expand partial_treebox_rep;
                                       Intros p_gggpar p_ggpl_or_r b_ggpar;
                                       assert_PROP(is_pointer_or_null p_ggpar) by entailer!;
                                       assert_PROP(is_pointer_or_null p_ggpl_or_r) by entailer!.
                                     -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                       rename p_ggpl_or_r into p_ggpl.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpl <> p_gpar).
                                       destruct H25.
                                       destruct H26. 
                                       2:{ assert(p_ggpl = p_gpar) by tauto.
                                           destruct tree_ggpl; simpl.
                                           { assert_PROP (p_ggpl = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b c d. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 3.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpl <> p_gpar *)
                                       destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                       *****
                                         rewrite <- ETree_runc.
                                         expand rbtree_rep.
                                         forward_call(
                                           p_par_med, p_gpar, p_ggpar, p_rsib,
                                           p_med, p_runc, p_ggpar, nullval, 
                                           BlackNode node_par, RedNode node_gpar,
                                           tree_med, tree_runc, tree_rsib,
                                           root, true,
                                           false, p_gggpar, p_ggpl, node_ggpar,
                                           true, E).
                                         { entailer!. expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                         rewrite <- H3.
                                         Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r)))
                                                  [(L, node_ggpar, E)]
                                                  (field_address t_struct_tree [StructField _right] p_ggpar)
                                                  p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_runc.
                                         destruct node_runc as[c_runc k_runc v_runc].
                                         assert(c_runc = Black)by auto.
                                         subst c_runc.
                                         unfold r_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         remember (T lch node_med rch) as tree_med.
                                         expand rbtree_rep. Intros a b.
                                         Exists p_med p_gpar p_rsib p_runc a b.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         rewrite <- ETree_runc.
                                         forward_call(
                                           p_par_med, p_gpar, p_ggpar, p_rsib,
                                           p_med, p_runc, p_ggpar, nullval, 
                                           BlackNode node_par, RedNode node_gpar,
                                           tree_med, tree_runc, tree_rsib,
                                           root, true,
                                           false, p_gggpar, p_ggpl, node_ggpar,
                                           false, tree_ggpl).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpl.
                                           expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                         rewrite <- H3.
                                         Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r)))
                                                [(L, node_ggpar, tree_ggpl)]
                                                (field_address t_struct_tree [StructField _right] p_ggpar)
                                                p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_runc.
                                         destruct node_runc as[c_runc k_runc v_runc].
                                         assert(c_runc = Black)by auto.
                                         subst c_runc.
                                         unfold r_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpl b_ggpar. entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer!.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) as node_runc.
                                         remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                         expand rbtree_rep.
                                         Exists p_med p_gpar p_rsib p_runc.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpl <> p_gpar).
                                         destruct H24. 
                                         2:{ assert(p_ggpl = p_gpar) by tauto.
                                             destruct tree_ggpl; expand rbtree_rep.
                                             { assert_PROP (p_ggpl = nullval) by entailer!.
                                               subst. congruence. }
                                             Intros a b c d. subst.
                                             assert_PROP False;[|contradiction].
                                             focus_SEP 3.
                                             sep_apply data_at_conflict;auto.
                                             entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         *****
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r)))
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_med p_gpar p_rsib p_runc a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r)))
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib p_runc.
                                                  entailer!.
                                             *****
                                               Intros p_ans_another_child p_ans.
                                               destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r)))
                                                       ((L, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_med p_gpar p_rsib p_runc a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       false, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                       ((L, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _right] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib p_runc.
                                                  entailer!.
                                                  }
                                     -----
                                       rename Tree_ggpl_Or_ggpr into tree_ggpl.
                                       rename p_ggpl_or_r into p_ggpl.
                                       rewrite partial_treebox_rep''.
                                       destruct (rev l) eqn:El.
                                       (* El : rev l = [] *)
                                       { assert (l = [])by (apply rev_nil_elim in El; auto).
                                         assert_PROP (p_gggpar = nullval /\ root = b_ggpar). 
                                         { expand partial_treebox_rep_topdown. entailer!. }
                                       expand partial_treebox_rep_topdown.
                                       pose proof classic (p_ggpl <> p_gpar).
                                       destruct H25.
                                       destruct H26. 
                                       2:{ assert(p_ggpl = p_gpar) by tauto.
                                           destruct tree_ggpl; simpl.
                                           { assert_PROP (p_ggpl = nullval) by entailer!.
                                             subst. congruence. }
                                           Intros a b c d. subst.
                                           assert_PROP False;[|contradiction].
                                           focus_SEP 3.
                                           sep_apply data_at_conflict;auto.
                                           entailer!. }
                                       (* p_ggpl <> p_gpar *)
                                       destruct tree_ggpl as[|? ? ?] eqn:Tree.
                                       *****
                                         rewrite <- ETree_runc.
                                         expand rbtree_rep.
                                         forward_call(
                                           p_par_med, p_gpar, p_ggpar, p_rsib,
                                           p_med, p_runc, p_ggpar, nullval, 
                                           BlackNode node_par, RedNode node_gpar,
                                           tree_med, tree_runc, tree_rsib,
                                           root, true,
                                           true, p_gggpar, p_ggpl, node_ggpar,
                                           true, E).
                                         { entailer!. expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                         rewrite <- H3.
                                         Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                  [(R, node_ggpar, E)]
                                                  (field_address t_struct_tree [StructField _left] p_ggpar)
                                                  p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par.
                                         rewrite Heqtree_runc.
                                         destruct node_runc as[c_runc k_runc v_runc].
                                         assert(c_runc = Black)by auto.
                                         subst c_runc.
                                         unfold r_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval nullval b_ggpar.
                                         entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer.
                                         remember (T lch node_med rch) as tree_med.
                                         expand rbtree_rep. Intros a b.
                                         Exists p_med p_gpar p_rsib p_runc a b.
                                         entailer!.
                                       *****
                                         rewrite <- Tree.
                                         rewrite <- ETree_runc.
                                         forward_call(
                                           p_par_med, p_gpar, p_ggpar, p_rsib,
                                           p_med, p_runc, p_ggpar, nullval, 
                                           BlackNode node_par, RedNode node_gpar,
                                           tree_med, tree_runc, tree_rsib,
                                           root, true,
                                           true, p_gggpar, p_ggpl, node_ggpar,
                                           false, tree_ggpl).
                                         { entailer!. 
                                           remember ((T t3 n0 t4)) as tree_ggpl.
                                           expand rbtree_rep.
                                           Exists p_lch p_rch; entailer!.
                                           unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                           entailer!. }
                                         { repeat split; try tauto; subst; auto. intros. congruence. }
                                         forward.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                         rewrite <- H3.
                                         Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                [(R, node_ggpar, tree_ggpl)]
                                                (field_address t_struct_tree [StructField _left] p_ggpar)
                                                p_ggpar.
                                         expand balance'.
                                         rewrite Ecolor_par. rewrite Heqtree_runc.
                                         destruct node_runc as[c_runc k_runc v_runc].
                                         assert(c_runc = Black)by auto.
                                         subst c_runc.
                                         unfold r_rotate.
                                         expand partial_treebox_rep.
                                         Exists nullval p_ggpl b_ggpar. entailer!.
                                         expand treebox_rep.
                                         Exists p_par_med.
                                         unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                         entailer!.
                                         remember (T lch node_med rch) as tree_med.
                                         remember (T t3 n0 t4) as tree_ggpl.
                                         remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) as node_runc.
                                         remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                         expand rbtree_rep.
                                         Exists p_med p_gpar p_rsib p_runc.
                                         entailer!.
                                       }
                                       (* El : rev l = h2 :: l0 *)
                                       { pose proof classic (p_ggpl <> p_gpar).
                                         destruct H24. 
                                         2:{ assert(p_ggpl = p_gpar) by tauto.
                                             destruct tree_ggpl; expand rbtree_rep.
                                             { assert_PROP (p_ggpl = nullval) by entailer!.
                                               subst. congruence. }
                                             Intros a b c d. subst.
                                             assert_PROP False;[|contradiction].
                                             focus_SEP 3.
                                             sep_apply data_at_conflict;auto.
                                             entailer!. }
                                         destruct h2 as [[LR_ans node_ans] tree_ans_another_child].
                                         expand partial_treebox_rep_topdown.
                                         destruct LR_ans. 
                                         *****
                                                Intros p_ans_another_child p_ans.
                                                destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_med p_gpar p_rsib p_runc a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                       ((R, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib p_runc.
                                                  entailer!.
                                             *****
                                               Intros p_ans_another_child p_ans.
                                               destruct tree_ggpl as[|] eqn:Tree.
                                                ------
                                                  assert_PROP(p_ggpl = nullval).
                                                  { expand rbtree_rep. entailer!. }
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       true, E).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  try remember (T lch node_med rch) as tree_med.
                                                  remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                       ((R, node_ggpar, E) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar nullval b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  try remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc.
                                                  expand rbtree_rep.
                                                  Intros a b.
                                                  Exists p_med p_gpar p_rsib p_runc a b.
                                                  entailer!.
                                              ------
                                                  rewrite <- Tree.
                                                  forward_call(
                                                       p_par_med, p_gpar, p_ggpar, p_rsib,
                                                       p_med, p_runc, p_ans, nullval, 
                                                       BlackNode node_par, RedNode node_gpar,
                                                       tree_med, tree_runc, tree_rsib,
                                                       root, true,
                                                       true, p_gggpar, p_ggpl, node_ggpar,
                                                       false, tree_ggpl).
                                                  { entailer!. expand rbtree_rep.
                                                    Exists p_lch p_rch; entailer!.
                                                    unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                    entailer!. }
                                                  { repeat split; try tauto; subst; auto. intros. congruence. }
                                                  Intros.
                                                  gather_SEP 5 9 10 11 12 13 14 15.
                                                  replace_SEP 0 
                                                  (partial_treebox_rep_topdown
                                                     (rev l)
                                                     root b_ggpar p_gggpar nullval).
                                                  { rewrite El.
                                                    expand partial_treebox_rep_topdown.
                                                    entailer!.
                                                    Exists p_ans_another_child p_ans.
                                                    entailer!. }
                                                  rewrite <- partial_treebox_rep''.
                                                  forward.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  Exists (T tree_med (BlackNode node_par)
                                      (T tree_rsib (RedNode node_gpar)
                                      (T tree_runc_l node_runc tree_runc_r))) 
                                                       ((R, node_ggpar, tree_ggpl) :: l)
                                                       (field_address t_struct_tree [StructField _left] p_ggpar)
                                                       p_ggpar.
                                                  rewrite <- H3.
                                                  expand balance'.
                                                  rewrite Ecolor_par. rewrite Heqtree_runc.
                                                  destruct node_runc as[c_runc k_runc v_runc].
                                                  assert(c_runc = Black)by auto.
                                                  subst c_runc.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  unfold r_rotate.
                                                  expand partial_treebox_rep.
                                                  Exists p_gggpar p_ggpl b_ggpar.
                                                  expand treebox_rep.
                                                  Exists p_par_med.
                                                  unfold_data_at (data_at _ t_struct_tree _ p_ggpar).
                                                  entailer!.
                                                  repeat remember (T lch node_med rch) as tree_med +
                                                    remember ({| color_of_node := Black; key_of_node := k_runc; value_of_node := v_runc |}) 
                                                      as node_runc +
                                                    remember (T tree_runc_l node_runc tree_runc_r) as tree_runc +
                                                    remember (T t3 n0 t4) as tree_ggpl.
                                                  expand rbtree_rep.
                                                  Exists p_med p_gpar p_rsib p_runc.
                                                  entailer!. }
Qed.
End insertBalance.