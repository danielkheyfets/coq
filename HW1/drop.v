Set Warnings "-notation-overridden,-parsing".

From LF Require Export Poly.

Fixpoint posfix {X : Type} (n : nat) (l : list X) : list X :=
    match l with
    | [] => []
    | s ::ss => match n with
            | O => s :: ss
            | S n' => posfix n' ss
            end
    end.


    
Fixpoint nthe {X : Type} (n : nat) (l : list X) : list X :=
    match l with
    | [] => []
    | s ::ss => match n with
            | O => []
            | S n' => s :: (nthe n' ss)
            end
    end.


Definition drop {X : Type} (n m : nat) (l : list X) : list X :=
    match m with
    | O => (nthe n l)
    | S m' => (nthe n (posfix m l))
    end.



Example tast_drop1: drop 3 0 [1;2;3;4;5] = [1;2;3].
    reflexivity. Qed.

Example tast_drop2: drop  3 1  [1;2;3;4;5] = [2;3;4].
    reflexivity. Qed.

Example tast_drop3: drop 3 100  [1;2;3;4;5] = [].
    reflexivity. Qed.

Example tast_drop4: drop  30 0 [1;2;3;4;5] = [1;2;3;4;5].
    reflexivity. Qed.

Example tast_drop5: drop  30 2 [1;2;3;4;5] = [3;4;5].
    reflexivity. Qed.

Example tast_drop6: drop   30 2 [1] = [].
    reflexivity. Qed.

Example tast_drop7: drop   30 2 [1;1;1] = [1].
    reflexivity. Qed.

Example tast_drop8: drop   3 2 [7;8;20;2;11;15;6] = [20;2;11].
    reflexivity. Qed.

Example tast_drop9z: drop   2 3 [1;2;3;4] = [4].
    reflexivity. Qed.

Theorem nthe_empty: forall (X : Type) (m : nat), nthe m ([] : list X) = [].
Proof.
  intros X m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem posfix_empty: forall (X : Type) (m : nat), posfix m ([] : list X) = [].
Proof.
  intros X m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem nthe_zero :forall (X : Type) (m : nat) (l: list X), nthe 0 l = [].
Proof.
  intros X m l .
  induction l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem drop_empty: forall (X : Type) (n m : nat) , drop n m ([] : list X) = [].
    Proof.
      intros X n m .
      simpl. induction m as [|n' ih]. 
      - simpl. rewrite nthe_empty. reflexivity.
      - simpl. rewrite nthe_empty. reflexivity.
    Qed.

Theorem drop_zero: forall (X : Type) (n : nat) (l : list X), drop 0 n l = [].
    Proof.
      intros X n l.
      simpl. destruct n. 
      - simpl. destruct l.
                + reflexivity.
                + reflexivity.
      - simpl. destruct l.
                + reflexivity.
                + simpl. {destruct (posfix n l). reflexivity.
                        - reflexivity.
                }
    Qed.

Theorem rev_length : forall (X : Type) (l : list X) , 
    length (rev l) = length l.
  Proof.
    intros X l. induction l as [| n l' IHl'].
    - (* l = nil *)
      reflexivity.
    - (* l = cons *)
      simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'. rewrite plus_comm.
      reflexivity.
  Qed.

(**THEROM 1*)
Theorem drop_zero_empty: forall (X : Type) (n m : nat) (l : list X), drop n m ([] : list X) = drop 0 m l.
    Proof.
      intros X n m l.
      rewrite drop_zero. rewrite drop_empty. reflexivity.
    Qed.


(**THEROM 2*)
Theorem rev_length_drop_cons: forall (X: Type) ( n : nat) (l : list X) (m : X),
   length( rev (m :: (drop n 0 l))) =  length( ((drop  (n + 1) 0 (m :: l)))).
   Proof.

   intros X n l m. destruct l as [|l'].
    - rewrite drop_empty. simpl. rewrite plus_comm. simpl. rewrite nthe_empty. reflexivity.
    - rewrite plus_comm.  simpl.  rewrite app_length. simpl. rewrite  rev_length. rewrite plus_comm. simpl. reflexivity.
    Qed.
 
 