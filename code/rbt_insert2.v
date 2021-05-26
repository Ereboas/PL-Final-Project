From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "rbt_insert.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 16%positive.
Definition ___builtin_annot_intval : ident := 17%positive.
Definition ___builtin_bswap : ident := 9%positive.
Definition ___builtin_bswap16 : ident := 11%positive.
Definition ___builtin_bswap32 : ident := 10%positive.
Definition ___builtin_bswap64 : ident := 8%positive.
Definition ___builtin_clz : ident := 42%positive.
Definition ___builtin_clzl : ident := 43%positive.
Definition ___builtin_clzll : ident := 44%positive.
Definition ___builtin_ctz : ident := 45%positive.
Definition ___builtin_ctzl : ident := 46%positive.
Definition ___builtin_ctzll : ident := 47%positive.
Definition ___builtin_debug : ident := 58%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fmadd : ident := 50%positive.
Definition ___builtin_fmax : ident := 48%positive.
Definition ___builtin_fmin : ident := 49%positive.
Definition ___builtin_fmsub : ident := 51%positive.
Definition ___builtin_fnmadd : ident := 52%positive.
Definition ___builtin_fnmsub : ident := 53%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 18%positive.
Definition ___builtin_memcpy_aligned : ident := 14%positive.
Definition ___builtin_read16_reversed : ident := 54%positive.
Definition ___builtin_read32_reversed : ident := 55%positive.
Definition ___builtin_sel : ident := 15%positive.
Definition ___builtin_va_arg : ident := 20%positive.
Definition ___builtin_va_copy : ident := 21%positive.
Definition ___builtin_va_end : ident := 22%positive.
Definition ___builtin_va_start : ident := 19%positive.
Definition ___builtin_write16_reversed : ident := 56%positive.
Definition ___builtin_write32_reversed : ident := 57%positive.
Definition ___compcert_i64_dtos : ident := 27%positive.
Definition ___compcert_i64_dtou : ident := 28%positive.
Definition ___compcert_i64_sar : ident := 39%positive.
Definition ___compcert_i64_sdiv : ident := 33%positive.
Definition ___compcert_i64_shl : ident := 37%positive.
Definition ___compcert_i64_shr : ident := 38%positive.
Definition ___compcert_i64_smod : ident := 35%positive.
Definition ___compcert_i64_smulh : ident := 40%positive.
Definition ___compcert_i64_stod : ident := 29%positive.
Definition ___compcert_i64_stof : ident := 31%positive.
Definition ___compcert_i64_udiv : ident := 34%positive.
Definition ___compcert_i64_umod : ident := 36%positive.
Definition ___compcert_i64_umulh : ident := 41%positive.
Definition ___compcert_i64_utod : ident := 30%positive.
Definition ___compcert_i64_utof : ident := 32%positive.
Definition ___compcert_va_composite : ident := 26%positive.
Definition ___compcert_va_float64 : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 23%positive.
Definition ___compcert_va_int64 : ident := 24%positive.
Definition _color : ident := 1%positive.
Definition _get_color1 : ident := 61%positive.
Definition _get_color2 : ident := 62%positive.
Definition _insert : ident := 81%positive.
Definition _insert_balance : ident := 77%positive.
Definition _key : ident := 2%positive.
Definition _l : ident := 65%positive.
Definition _l_par : ident := 69%positive.
Definition _last_node : ident := 79%positive.
Definition _left : ident := 5%positive.
Definition _left_rotate : ident := 68%positive.
Definition _left_rotate_wrap : ident := 70%positive.
Definition _main : ident := 82%positive.
Definition _make_black : ident := 64%positive.
Definition _mallocN : ident := 59%positive.
Definition _mid : ident := 67%positive.
Definition _p : ident := 60%positive.
Definition _p_gpar : ident := 76%positive.
Definition _p_par : ident := 75%positive.
Definition _par : ident := 7%positive.
Definition _r : ident := 66%positive.
Definition _r_par : ident := 72%positive.
Definition _right : ident := 6%positive.
Definition _right_rotate : ident := 71%positive.
Definition _right_rotate_wrap : ident := 73%positive.
Definition _root : ident := 63%positive.
Definition _t : ident := 74%positive.
Definition _tree : ident := 4%positive.
Definition _value : ident := 3%positive.
Definition _x : ident := 78%positive.
Definition _y : ident := 80%positive.
Definition _t'1 : ident := 83%positive.
Definition _t'10 : ident := 92%positive.
Definition _t'11 : ident := 93%positive.
Definition _t'12 : ident := 94%positive.
Definition _t'2 : ident := 84%positive.
Definition _t'3 : ident := 85%positive.
Definition _t'4 : ident := 86%positive.
Definition _t'5 : ident := 87%positive.
Definition _t'6 : ident := 88%positive.
Definition _t'7 : ident := 89%positive.
Definition _t'8 : ident := 90%positive.
Definition _t'9 : ident := 91%positive.

Definition f_get_color1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _color tint))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_get_color2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _color tint))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_make_black := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq
               (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn None)
  (Ssequence
    (Sset _p
      (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
        (tptr (Tstruct _tree noattr))))
    (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn None)
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _color tint)
        (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_left_rotate := {|
  fn_return := (tptr (Tstruct _tree noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _tree noattr))) ::
               (_mid, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _r
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Sset _mid
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr)))
        (Etempvar _mid (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr)))
          (Etempvar _l (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _r (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sifthenelse (Ebinop One
                             (Etempvar _mid (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mid (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _par
                    (tptr (Tstruct _tree noattr)))
                  (Etempvar _l (tptr (Tstruct _tree noattr))))
                Sskip)
              (Sreturn (Some (Etempvar _r (tptr (Tstruct _tree noattr))))))))))))
|}.

Definition f_left_rotate_wrap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _tree noattr))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l_par, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'4
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _left_rotate (Tfunction
                             (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                             (tptr (Tstruct _tree noattr)) cc_default))
        ((Etempvar _l (tptr (Tstruct _tree noattr))) :: nil))
      (Sassign
        (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr)))
        (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
    (Ssequence
      (Sset _l_par
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _l_par (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _t'5 (tptr (Tstruct _tree noattr)))
                       (Etempvar _l (tptr (Tstruct _tree noattr))) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _left_rotate (Tfunction
                                   (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                                   (tptr (Tstruct _tree noattr)) cc_default))
              ((Etempvar _l (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _l_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'2 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _left_rotate (Tfunction
                                   (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                                   (tptr (Tstruct _tree noattr)) cc_default))
              ((Etempvar _l (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _l_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'3 (tptr (Tstruct _tree noattr))))))))))
|}.

Definition f_right_rotate := {|
  fn_return := (tptr (Tstruct _tree noattr));
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _tree noattr))) ::
               (_mid, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Sset _mid
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr)))
        (Etempvar _mid (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr)))
          (Etempvar _r (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _l (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sifthenelse (Ebinop One
                             (Etempvar _mid (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mid (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _par
                    (tptr (Tstruct _tree noattr)))
                  (Etempvar _r (tptr (Tstruct _tree noattr))))
                Sskip)
              (Sreturn (Some (Etempvar _l (tptr (Tstruct _tree noattr))))))))))))
|}.

Definition f_right_rotate_wrap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _tree noattr))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r_par, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'4
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _right_rotate (Tfunction
                              (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                              (tptr (Tstruct _tree noattr)) cc_default))
        ((Etempvar _r (tptr (Tstruct _tree noattr))) :: nil))
      (Sassign
        (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr)))
        (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
    (Ssequence
      (Sset _r_par
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _r_par (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _t'5 (tptr (Tstruct _tree noattr)))
                       (Etempvar _r (tptr (Tstruct _tree noattr))) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _right_rotate (Tfunction
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      Tnil) (tptr (Tstruct _tree noattr))
                                    cc_default))
              ((Etempvar _r (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _r_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'2 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _right_rotate (Tfunction
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      Tnil) (tptr (Tstruct _tree noattr))
                                    cc_default))
              ((Etempvar _r (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _r_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'3 (tptr (Tstruct _tree noattr))))))))))
|}.

Definition f_insert_balance := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) ::
               (_p_par, (tptr (Tstruct _tree noattr))) ::
               (_p_gpar, (tptr (Tstruct _tree noattr))) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, tint) :: (_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'12, (tptr (Tstruct _tree noattr))) ::
               (_t'11, (tptr (Tstruct _tree noattr))) ::
               (_t'10, (tptr (Tstruct _tree noattr))) ::
               (_t'9, (tptr (Tstruct _tree noattr))) ::
               (_t'8, (tptr (Tstruct _tree noattr))) ::
               (_t'7, (tptr (Tstruct _tree noattr))) ::
               (_t'6, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
      (tptr (Tstruct _tree noattr))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _p_par
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Scall (Some _t'5)
            (Evar _get_color1 (Tfunction
                                (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                                tint cc_default))
            ((Etempvar _p_par (tptr (Tstruct _tree noattr))) :: nil))
          (Sifthenelse (Ebinop One (Etempvar _t'5 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Sreturn None)
            (Ssequence
              (Sset _p_gpar
                (Efield
                  (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _par
                  (tptr (Tstruct _tree noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sreturn None)
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _left
                      (tptr (Tstruct _tree noattr))))
                  (Sifthenelse (Ebinop Oeq
                                 (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                 (Etempvar _t'6 (tptr (Tstruct _tree noattr)))
                                 tint)
                    (Ssequence
                      (Ssequence
                        (Sset _t'12
                          (Efield
                            (Ederef
                              (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _right
                            (tptr (Tstruct _tree noattr))))
                        (Scall (Some _t'2)
                          (Evar _get_color2 (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _tree noattr))
                                                Tnil) tint cc_default))
                          ((Etempvar _t'12 (tptr (Tstruct _tree noattr))) ::
                           nil)))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                                     (Econst_int (Int.repr 1) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _tree noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'11 (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 0) tint)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 1) tint))
                              (Sset _p
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Sset _t'10
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _right
                                (tptr (Tstruct _tree noattr))))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _p (tptr (Tstruct _tree noattr)))
                                           (Etempvar _t'10 (tptr (Tstruct _tree noattr)))
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'1)
                                      (Evar _left_rotate (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _tree noattr))
                                                             Tnil)
                                                           (tptr (Tstruct _tree noattr))
                                                           cc_default))
                                      ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                       nil))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _left
                                        (tptr (Tstruct _tree noattr)))
                                      (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
                                  (Ssequence
                                    (Scall None
                                      (Evar _right_rotate_wrap (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _tree noattr))
                                                                   (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                      ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                       (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sreturn None))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Scall None
                                    (Evar _right_rotate_wrap (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _tree noattr))
                                                                 (Tcons
                                                                   (tptr (tptr (Tstruct _tree noattr)))
                                                                   Tnil))
                                                               tvoid
                                                               cc_default))
                                    ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                     (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                     nil))
                                  (Sreturn None))))))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _left
                            (tptr (Tstruct _tree noattr))))
                        (Scall (Some _t'4)
                          (Evar _get_color2 (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _tree noattr))
                                                Tnil) tint cc_default))
                          ((Etempvar _t'9 (tptr (Tstruct _tree noattr))) ::
                           nil)))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                                     (Econst_int (Int.repr 1) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _left
                                  (tptr (Tstruct _tree noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'8 (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 0) tint)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 1) tint))
                              (Sset _p
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _left
                                (tptr (Tstruct _tree noattr))))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _p (tptr (Tstruct _tree noattr)))
                                           (Etempvar _t'7 (tptr (Tstruct _tree noattr)))
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'3)
                                      (Evar _right_rotate (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _tree noattr))
                                                              Tnil)
                                                            (tptr (Tstruct _tree noattr))
                                                            cc_default))
                                      ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                       nil))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _right
                                        (tptr (Tstruct _tree noattr)))
                                      (Etempvar _t'3 (tptr (Tstruct _tree noattr)))))
                                  (Ssequence
                                    (Scall None
                                      (Evar _left_rotate_wrap (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _tree noattr))
                                                                  (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                      ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                       (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sreturn None))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Scall None
                                    (Evar _left_rotate_wrap (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _tree noattr))
                                                                (Tcons
                                                                  (tptr (tptr (Tstruct _tree noattr)))
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                    ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                     (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                     nil))
                                  (Sreturn None))))))))))))))))
    Sskip))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: (_x, tint) ::
                (_value, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_root, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_p, (tptr (Tstruct _tree noattr))) ::
               (_last_node, (tptr (Tstruct _tree noattr))) :: (_y, tint) ::
               (_t'1, (tptr tvoid)) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _root (Etempvar _t (tptr (tptr (Tstruct _tree noattr)))))
  (Ssequence
    (Sset _last_node (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Sset _p
              (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                (tptr (Tstruct _tree noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _p (tptr (Tstruct _tree noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                                     cc_default))
                    ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
                  (Sset _p
                    (Ecast (Etempvar _t'1 (tptr tvoid))
                      (tptr (Tstruct _tree noattr)))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _color tint)
                    (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _key tint)
                      (Etempvar _x tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value tuint)
                        (Etempvar _value tuint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _left
                            (tptr (Tstruct _tree noattr)))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _right
                              (tptr (Tstruct _tree noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _par
                                (tptr (Tstruct _tree noattr)))
                              (Etempvar _last_node (tptr (Tstruct _tree noattr))))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                  (tptr (Tstruct _tree noattr)))
                                (Etempvar _p (tptr (Tstruct _tree noattr))))
                              Sbreak))))))))
              (Ssequence
                (Sset _y
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _key tint))
                (Sifthenelse (Ebinop Oeq (Etempvar _x tint)
                               (Etempvar _y tint) tint)
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _value tuint)
                      (Etempvar _value tuint))
                    Sbreak)
                  (Ssequence
                    (Sset _last_node
                      (Etempvar _p (tptr (Tstruct _tree noattr))))
                    (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                                   (Etempvar _y tint) tint)
                      (Sset _t
                        (Eaddrof
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _left
                            (tptr (Tstruct _tree noattr)))
                          (tptr (tptr (Tstruct _tree noattr)))))
                      (Sset _t
                        (Eaddrof
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _right
                            (tptr (Tstruct _tree noattr)))
                          (tptr (tptr (Tstruct _tree noattr))))))))))))
        Sskip)
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _color tint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Scall None
              (Evar _insert_balance (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _tree noattr)))
                                        (Tcons
                                          (tptr (tptr (Tstruct _tree noattr)))
                                          Tnil)) tvoid cc_default))
              ((Etempvar _t (tptr (tptr (Tstruct _tree noattr)))) ::
               (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) :: nil))
            Sskip))
        (Scall None
          (Evar _make_black (Tfunction
                              (Tcons (tptr (tptr (Tstruct _tree noattr)))
                                Tnil) tvoid cc_default))
          ((Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) :: nil))))))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   ((_color, tint) :: (_key, tint) :: (_value, tuint) ::
    (_left, (tptr (Tstruct _tree noattr))) ::
    (_right, (tptr (Tstruct _tree noattr))) ::
    (_par, (tptr (Tstruct _tree noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_get_color1, Gfun(Internal f_get_color1)) ::
 (_get_color2, Gfun(Internal f_get_color2)) ::
 (_make_black, Gfun(Internal f_make_black)) ::
 (_left_rotate, Gfun(Internal f_left_rotate)) ::
 (_left_rotate_wrap, Gfun(Internal f_left_rotate_wrap)) ::
 (_right_rotate, Gfun(Internal f_right_rotate)) ::
 (_right_rotate_wrap, Gfun(Internal f_right_rotate_wrap)) ::
 (_insert_balance, Gfun(Internal f_insert_balance)) ::
 (_insert, Gfun(Internal f_insert)) :: nil).

Definition public_idents : list ident :=
(_insert :: _insert_balance :: _right_rotate_wrap :: _right_rotate ::
 _left_rotate_wrap :: _left_rotate :: _make_black :: _get_color2 ::
 _get_color1 :: _mallocN :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


