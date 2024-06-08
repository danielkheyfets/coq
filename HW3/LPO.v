(*
This question concerns the constructive universe, and in particular, it explores some of its
benefits in the context of synthetic computability. Specifically, the goal of this exercise is to
show that there can’t be a constructive proof that every enumerable predicate is decidable,
as this would induce a decider of the halting problem.
For a subset of the natural numbers (i.e., a predicate over the natural numbers) the properties
of being enumerable and being decidable can be formally stated in Coq as follows:
*)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import List Lia.

Definition enum_mono (P : nat -> Prop) :=
 exists e : nat -> nat, (forall k k', k <= k' -> e k <= e k') /\ forall
n, P n <-> exists k, e k = n.

Definition dec (P : nat -> Prop) :=
 exists d : nat -> bool, forall n, P n <-> d n = true.

 (*
 The limited principle of omniscience (LPO) states that the existential quantification of any
decidable proposition is again decidable. For the natural numbers, a functional variant this
principle can be formalized in Coq as follows:
 *)

 Definition LPO :=
  forall f : nat -> bool, (exists n, f n = true) \/ (forall n, f n =
 false).


(*
This statement is a common divider between constructive and classical mathematics.
Copy the above lines into your solution file.
1. Implement a function print f that induces a predicate P_print f such that
enum_mono (P_print f) holds and dec (P_print f) implies LPO.
Copy the code below to your solution file and complete the missing bits. To help you on
your quest, we supply one lemma you might want to use (but need to prove in order to
do so). You might need to come up with other helper lemmas yourself.
*)



Fixpoint print_rec (f : nat -> bool) (k : nat) : nat :=
  match k with
  | 0 => if f 0 then 1 else 0
  | S k' => if f k then 1 +  print_rec f k' else print_rec f k'
  end.

  Definition print (f : nat -> bool) (k : nat) : nat :=
  (print_rec f k).


 
  
  Lemma print_mono f k k' :
  k <= k' -> print f k <= print f k'.
  Proof.
  intros.
  generalize dependent H.
  induction k'; intros.
  - assert (k = 0). { lia. } rewrite H0. lia. 
  - assert(forall n m : nat, n <= m -> n < m \/ n = m) by lia. destruct(  H0 k (S k')  H).
    +  assert(k <= k'). {lia. } 
    specialize (IHk' H2). simpl.
      destruct (f  (S k')).
      ++ assert (print f k' < S (print f k')) by lia. lia. 
      ++ apply IHk'.
      + rewrite <- H1. lia.
Qed.


Definition P_print (f : nat -> bool) :=
 fun n => exists k, print f k = n.


(*
2. Copy the code below to your solution file and complete the missing bits.
*)

Lemma print_is_false_helper : forall (f : nat -> bool) (n : nat),
  (forall k : nat, k <= n -> f k = false) -> print f n = 0.
Proof.
  intros f n H.
  induction n as [| n' IHn'].
  - simpl. rewrite H. lia. lia. 
  - simpl. rewrite H.
    + apply IHn'. intros. apply H. lia.
    + lia.
Qed.

Lemma print_Sn_true_is_one_helper : forall (f : nat -> bool) (n : nat),
  f (S n) = true -> (forall k : nat, k <= n -> f k = false) -> print f (S n) = 1.
Proof.
intros f n H1 H2.
simpl.
rewrite H1.
rewrite print_is_false_helper. 
- reflexivity.
- apply H2.
Qed.


(* if print f k = 1 so we mast have n wich will make f n = true because of prit implementation we sum the amount of (f i) = true from 0 to k*)
 Lemma one_f_exists_print_helper : forall (f : nat -> bool),
 (exists k : nat, print f k = 1) -> (exists n : nat, f n = true).
 Proof.
  intros f [k H].
  generalize dependent H. generalize dependent f.
  induction k ; intros f Hp.
  - simpl in Hp.
    exists 0.
    destruct (f 0); [reflexivity | discriminate Hp].
  - simpl in Hp.
    destruct (f (S k)) eqn:PP.
    + exists (S k). apply PP.
    + apply IHk in Hp. apply Hp.
Qed.

Lemma eq_dec_helper : forall n m : nat, n = m \/ n <> m.
Proof.
  induction n as [| n IH].
  + destruct m as [| m].
    - left. lia.
    - right. lia.
  + destruct m as [| m].
    - right. lia. 
    - destruct (IH m) as [Heq | Hneq].
        -- left.  lia.
        -- right. lia.
Qed.



Theorem enum_mono_dec_LPO :
 (forall P, enum_mono P -> dec P) -> LPO.
Proof.
 intros H f. destruct (H (P_print f)) as [d Hd].
 - exists (print f). split; try apply print_mono. reflexivity.
 - destruct ( d 1)  eqn:nn.
 + left. apply (Hd 1) in nn. unfold P_print in nn. apply one_f_exists_print_helper in nn. apply nn.    
 + right. intro n. assert (Hp :  forall (k n  : nat), k  <=  n -> f k  = false). {
  intros. generalize dependent H0. generalize dependent k. induction n0. 
    -- intros. assert (k = 0). { lia. } rewrite H1.  specialize Hd with 1. destruct Hd.
    * destruct (f 0) eqn:hh. destruct (d 1)eqn:cc.
        ** apply nn.
        **  assert (false = true -> true = false). { lia. } apply H4. apply H2. unfold P_print. exists 0. unfold print. unfold print_rec. rewrite hh.  reflexivity. 
        ** reflexivity.
    -- intros. specialize Hd with 1. destruct (f k) eqn:hh.
     destruct (d 1)eqn:cc.
      ** rewrite nn. reflexivity.
      ** assert (false = true -> true = false). { lia. } apply H1. apply Hd. unfold P_print. assert(  k = (S n0)). {
      destruct (eq_dec_helper k (S n0)) as [H2 | H2].
        - apply H2.
        - assert (H3: k <= n0) by lia. specialize (IHn0 k H3). rewrite IHn0 in hh. discriminate. }
      ---  exists (S n0). rewrite H2 in hh. apply print_Sn_true_is_one_helper in hh.
        *** apply hh.
        *** intros. specialize IHn0 with k0. apply IHn0. apply H3.
      ** reflexivity.
 }
 specialize Hp with (n:= n) (k:=n). apply Hp. lia.
Qed.
