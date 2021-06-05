(* BEGIN AST *)

From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "linked_list_queue.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 7%positive.
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
Definition _back : ident := 5%positive.
Definition _exit : ident := 61%positive.
Definition _free : ident := 60%positive.
Definition _front : ident := 4%positive.
Definition _main : ident := 69%positive.
Definition _malloc : ident := 59%positive.
Definition _next : ident := 3%positive.
Definition _node : ident := 2%positive.
Definition _q : ident := 62%positive.
Definition _queue : ident := 6%positive.
Definition _queue_dequeue : ident := 68%positive.
Definition _queue_enqueue : ident := 67%positive.
Definition _queue_front : ident := 65%positive.
Definition _queue_init : ident := 63%positive.
Definition _queue_is_empty : ident := 64%positive.
Definition _t : ident := 66%positive.
Definition _value : ident := 1%positive.
Definition _t'1 : ident := 70%positive.
Definition _t'2 : ident := 71%positive.
Definition _t'3 : ident := 72%positive.
Definition _t'4 : ident := 73%positive.
Definition _t'5 : ident := 74%positive.
Definition _t'6 : ident := 75%positive.
Definition _t'7 : ident := 76%positive.

Definition f_queue_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr (Tstruct _queue noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
        (tptr (Tstruct _node noattr))))
    (Sassign
      (Efield
        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
          (Tstruct _queue noattr)) _back (tptr (Tstruct _node noattr)))
      (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
  (Sassign
    (Efield
      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
        (Tstruct _queue noattr)) _front (tptr (Tstruct _node noattr)))
    (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
|}.

Definition f_queue_is_empty := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr (Tstruct _queue noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
        (Tstruct _queue noattr)) _front (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Eunop Onotbool
                   (Etempvar _t'1 (tptr (Tstruct _node noattr))) tint))))
|}.

Definition f_queue_front := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr (Tstruct _queue noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
        (Tstruct _queue noattr)) _front (tptr (Tstruct _node noattr))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _t'1 (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _value tint))
    (Sreturn (Some (Etempvar _t'2 tint)))))
|}.

Definition f_queue_enqueue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr (Tstruct _queue noattr))) :: (_value, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _node noattr) tuint) :: nil))
    (Sset _t
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _t (tptr (Tstruct _node noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _value tint) (Etempvar _value tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _t (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                (Tstruct _queue noattr)) _back (tptr (Tstruct _node noattr))))
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _t'4 (tptr (Tstruct _node noattr))) tint)
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ecast (Etempvar _t (tptr (Tstruct _node noattr)))
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                      (Tstruct _queue noattr)) _back
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                    (Tstruct _queue noattr)) _front
                  (tptr (Tstruct _node noattr)))
                (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Ecast (Etempvar _t (tptr (Tstruct _node noattr)))
                    (tptr (Tstruct _node noattr))))
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _back
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _next
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _t'3 (tptr (Tstruct _node noattr))))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                    (Tstruct _queue noattr)) _back
                  (tptr (Tstruct _node noattr)))
                (Etempvar _t'3 (tptr (Tstruct _node noattr)))))))))))
|}.

Definition f_queue_dequeue := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr (Tstruct _queue noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_value, tint) :: (_t, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'7
      (Efield
        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
          (Tstruct _queue noattr)) _front (tptr (Tstruct _node noattr))))
    (Sset _value
      (Efield
        (Ederef (Etempvar _t'7 (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _value tint)))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
            (Tstruct _queue noattr)) _front (tptr (Tstruct _node noattr))))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _back (tptr (Tstruct _node noattr))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                       (Etempvar _t'5 (tptr (Tstruct _node noattr))) tint)
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                    (Tstruct _queue noattr)) _front
                  (tptr (Tstruct _node noattr))))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _t'6 (tptr (Tstruct _node noattr))) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Ecast
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _back
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                      (Tstruct _queue noattr)) _front
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
              (Sreturn (Some (Etempvar _value tint)))))
          Sskip)))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _front (tptr (Tstruct _node noattr))))
        (Sset _t
          (Efield
            (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                (Tstruct _queue noattr)) _front
              (tptr (Tstruct _node noattr))))
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _t'2 (tptr (Tstruct _node noattr))) :: nil)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                (Tstruct _queue noattr)) _front
              (tptr (Tstruct _node noattr)))
            (Etempvar _t (tptr (Tstruct _node noattr))))
          (Sreturn (Some (Etempvar _value tint))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   ((_value, tint) :: (_next, (tptr (Tstruct _node noattr))) :: nil)
   noattr ::
 Composite _queue Struct
   ((_front, (tptr (Tstruct _node noattr))) ::
    (_back, (tptr (Tstruct _node noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_queue_init, Gfun(Internal f_queue_init)) ::
 (_queue_is_empty, Gfun(Internal f_queue_is_empty)) ::
 (_queue_front, Gfun(Internal f_queue_front)) ::
 (_queue_enqueue, Gfun(Internal f_queue_enqueue)) ::
 (_queue_dequeue, Gfun(Internal f_queue_dequeue)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _queue_dequeue :: _queue_enqueue :: _queue_front ::
 _queue_is_empty :: _queue_init :: _exit :: _free :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.

(* END AST *)

Require Import VST.floyd.proofauto VST.floyd.library Coq.Lists.List.
Import ListNotations.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Fixpoint listrep (il: list Z) (p: val) : mpred :=
 match il with
 | i::il' => EX y: val,
        malloc_token Ews (Tstruct _node noattr) p *
        data_at Ews (Tstruct _node noattr) (Vint (Int.repr i),y) p *
        listrep il' y
 | nil => !! (p = nullval) && emp
 end.

Arguments listrep il p : simpl never.

Definition queue (il: list Z) (p: val) :=
  match il with
  | [] => data_at Ews (Tstruct _queue noattr) (nullval, nullval) p
  | (_ :: _) => EX front back : val,
    data_at Ews (Tstruct _queue noattr) (front, back) p *
    (listrep il front && listrep [last il 0] back)
  end.

Arguments queue il p : simpl never.

Definition queue_init_spec : ident * funspec :=
  DECLARE _queue_init
  WITH q : val
  PRE [tptr (Tstruct _queue noattr)]
    PROP () PARAMS (q) SEP (data_at_ Ews (Tstruct _queue noattr) q)
  POST [tvoid]
    PROP () RETURN () SEP (queue [] q).

Definition queue_is_empty_spec : ident * funspec :=
  DECLARE _queue_is_empty
  WITH q : val, il : list Z
  PRE [tptr (Tstruct _queue noattr)]
    PROP () PARAMS (q) SEP (queue il q)
  POST [tint]
    PROP ()
    RETURN (Vint (Int.repr (if eq_dec il [] then 1 else 0)))
    SEP (queue il q).

Definition queue_front_spec : ident * funspec :=
  DECLARE _queue_front
  WITH q : val, i : Z, il : list Z
  PRE [tptr (Tstruct _queue noattr)]
    PROP () PARAMS (q) SEP (queue (i :: il) q)
  POST [tint]
    PROP () RETURN (Vint (Int.repr i)) SEP (queue (i :: il) q).

Definition queue_enqueue_spec : ident * funspec :=
  DECLARE _queue_enqueue
  WITH q : val, i : Z, il : list Z, gv : globals
  PRE [ tptr (Tstruct _queue noattr), tint ]
    PROP (Int.min_signed <= i <= Int.max_signed)
    PARAMS (q; Vint (Int.repr i)) GLOBALS (gv)
    SEP (queue il q; mem_mgr gv)
  POST [tvoid]
    PROP () RETURN () SEP (queue (il ++ [i]) q; mem_mgr gv).

Definition queue_dequeue_spec : ident * funspec :=
  DECLARE _queue_dequeue
  WITH q : val, i : Z, il : list Z, gv : globals
  PRE [ tptr (Tstruct _queue noattr) ]
    PROP () PARAMS (q) GLOBALS (gv)
    SEP (queue (i :: il) q; mem_mgr gv)
  POST [tint]
    PROP ()
    RETURN (Vint (Int.repr i))
    SEP (queue il q; mem_mgr gv).

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    queue_init_spec;
    queue_is_empty_spec;
    queue_front_spec;
    queue_enqueue_spec;
    queue_dequeue_spec
  ]).