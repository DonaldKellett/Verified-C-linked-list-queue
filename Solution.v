Require Import Preloaded VST.floyd.proofauto VST.floyd.library.

Lemma listrep_local_prop: forall il p, listrep il p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> il=nil)).
Proof.
  induction il; intros; unfold listrep; fold listrep.
  - entailer!; split; auto.
  - Intros y.
    entailer!.
    split; intros; try discriminate; subst p.
    eapply field_compatible_nullval; eauto.
Qed.
#[export] Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
   listrep il p |-- valid_pointer p.
Proof.
  destruct il; intros; unfold listrep; fold listrep.
  - entailer!.
  - Intros y; entailer!.
Qed.
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma queue_local_prop: forall il p, queue il p |--  !! (isptr p).
Proof.
  intros; unfold queue.
  destruct il.
  - entailer!.
  - Intros front back; entailer!.
Qed.
#[export] Hint Resolve queue_local_prop : saturate_local.

Lemma queue_valid_pointer:
  forall il p,
   queue il p |-- valid_pointer p.
Proof.
  intros; unfold queue.
  destruct il.
  - entailer!.
  - Intros front back; entailer!.
Qed.
#[export] Hint Resolve queue_valid_pointer : valid_pointer.

Lemma body_queue_init : semax_body Vprog Gprog f_queue_init queue_init_spec.
Proof. start_function; do 3 forward; unfold queue; entailer!. Qed.

Lemma body_queue_is_empty :
  semax_body Vprog Gprog f_queue_is_empty queue_is_empty_spec.
Proof.
  start_function.
  unfold queue.
  destruct il.
  - do 2 forward.
  - Intros front back.
    forward.
    + unfold listrep; fold listrep.
      Intros y y0; subst y0.
      autorewrite with norm.
      assert_PROP (isptr front) by (rewrite (data_at_isptr _ _ _ front);
        entailer!).
      entailer!.
    + forward.
      unfold queue; unfold listrep; fold listrep.
      Intros y y0; subst y0.
      destruct (eq_dec (z :: il) []) as [Econtra | E]; try discriminate; clear E.
      Exists front back y nullval.
      assert_PROP (isptr front) by (rewrite (data_at_isptr _ _ _ front);
        entailer!).
      entailer!.
      destruct front; unfold isptr in H1; try now exfalso.
      auto.
Qed.

Lemma body_queue_front : semax_body Vprog Gprog f_queue_front queue_front_spec.
Proof.
  start_function.
  unfold queue; unfold listrep; fold listrep.
  Intros front back y y0; subst y0.
  forward.
  - autorewrite with norm.
    assert_PROP (isptr front) by (rewrite (data_at_isptr _ _ _ front);
      entailer!).
    entailer!.
  - autorewrite with norm.
    Fail forward.
    admit.
Admitted.

Lemma body_queue_enqueue :
  semax_body Vprog Gprog f_queue_enqueue queue_enqueue_spec.
Proof.
  start_function.
Admitted.

Lemma body_queue_dequeue :
  semax_body Vprog Gprog f_queue_dequeue queue_dequeue_spec.
Proof.
  start_function.
Admitted.