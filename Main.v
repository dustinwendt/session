(* Syntax of GV Terms and Types *) 

(* Add LoadPath "~/session/dblib/src". *)
Require Import List.
Require Import EqNat.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Dblib.Environments.
Check lookup_insert_recent.
(* Require Import DblibTactics.
Require Import Debruijn *)

Notation "[ ]" := nil : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Fixpoint delete {A : Type} (x : nat) (e : env A) : env A :=
  match x, e with
  | _, nil => nil
  | 0, (_ :: e) => e
  | (S n'), (e :: es) =>  delete n' es
  end.

Fixpoint update {A : Type} (x : nat) (o : option A) (e : env A) : env A :=
  match x, e with
  | 0, nil => nil
  | 0, (_ :: xs) => o :: xs
  | S n', nil => nil
  | S n', (x :: xs) => x :: (update n' o xs)
  end.

Inductive type : Set :=
| TSession :> stype -> type
| T1Nul : type
| TProd : type -> type -> type
| T0Nul : type
| TSum : type -> type -> type
| TLoli : type -> type -> type
with stype : Set :=
|TSendEnd : stype
|TRecvEnd : stype
|TSend : type -> stype -> stype
|TRecv : type -> stype -> stype.
(* |TSharp : stype.*)
            (*
with ltype : Prop :=
| lAllow : type -> type -> ltype.
             *)

Inductive constant : Set :=
| send : constant
| receive : constant
| fork : constant
| wait : constant
| link : constant.

Inductive term : Set :=
| EVar : nat -> term
| ECApp : constant -> term -> term
| ELam : term -> term
| EApp : term -> term -> term
| EPair : term -> term -> term
| ELetPair : nat -> nat -> term -> term -> term
| EInl : term -> term
| EInr : term -> term
| ECase : term -> term -> term -> term
| EUnit : term
| ELetUnit : term -> term -> term
| EAbsurd : term -> term.

Check (@lift term).
Eval cbv in (shift 0 (ELam (EVar 0))).

Notation "T * S" := (TProd T S).
Notation "T -o U" := (TLoli T U) (at level 0, right associativity).
Notation "! T ; S" := (TSend T S) (at level 0).
Notation "? T ; S" := (TRecv T S) (at level 0).
Notation "end!" := TSendEnd.
Notation "end?" := TRecvEnd.

Definition Env := env type.

Fixpoint dual(s:stype):stype:=
 match s with
 | end! => end?
 | end? => end!
 | ! T; s => ? T; (dual s)
 | ? T; s => ! T; (dual s)
 end.

Lemma dual_inverse : forall s, dual (dual s) = s.
Proof. induction s; simpl; try rewrite IHs; try reflexivity. Qed.

Instance Var_term : Var term := {
  var := EVar
                               }.

Fixpoint traverse_term (f : nat -> nat -> term) l t :=
  match t with
  | EVar x => f l x
  | ECApp c t => ECApp c (traverse_term f l t)
  | ELam t => ELam (traverse_term f (1+l) t)
  | EApp t1 t2 => EApp (traverse_term f l t1) (traverse_term f l t2)
  | EPair t1 t2 => EPair (traverse_term f l t1) (traverse_term f l t2)
  | ELetPair v1 v2 t1 t2 => ELetPair v1 v2 (traverse_term f l t1) (traverse_term f l t2)
  | EInl t => EInl (traverse_term f l t)
  | EInr t => EInr (traverse_term f l t)
  | ECase t t1 t2 => ECase (traverse_term f l t) (traverse_term f l t1) (traverse_term f l t2)
  | EUnit => EUnit
  | ELetUnit M N => ELetUnit (traverse_term f l M) (traverse_term f l N)
  | EAbsurd M => EAbsurd (traverse_term f l M)
  end.

Notation "()" := EUnit.

Instance Traverse_term : Traverse term term := {
                                                traverse := traverse_term
                                              }.

Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof. constructor. prove_traverse_var_injective. Qed.

Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof. constructor. prove_traverse_functorial. Qed.

Instance TraverseRelative_term : @TraverseRelative term term _.
Proof. constructor. prove_traverse_relative. Qed.

Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof. constructor. prove_traverse_identifies_var. Qed.

Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof. constructor. prove_traverse_var_is_identity. Qed.

Inductive value : term -> Prop :=
| VVar : forall x, value (EVar x)
| VAbs : forall M, value (ELam M)
| VNul : value EUnit
| VPair : forall V W, value V -> value W -> value (EPair V W)
| VInl : forall V, value V -> value (EInl V)
| VInr : forall V, value V -> value (EInr V).

(* 
(* GV Constants *)
Definition send_type{S : stype}{T : type} := ((TProd T (! T;S)) -o S).
Definition rec_type{S : stype}{T : type} := (? T;S) -o (TProd T S).
Definition fork_type{S : stype} := ((S -o end!) -o (dual S)).
Definition wait_type := end? -o T1Nul.
Definition link_type{S : stype} := (TProd S (dual S)) -o end!.
*)

Fixpoint tl_error{A} (x : list A): option (list A):=
  match x with
  | [] => None
  | (_ :: xs) => Some xs
  end.

Inductive check: Env -> term -> Env -> type -> Prop :=
| CVar : forall E x T, lookup x E = Some T ->
                  check E (EVar x) (update x None E) T
| CLam : forall E E' E'' M T U, check (insert 0 T E) M E' U ->
                       tl_error E' = Some E'' ->
                       check E (ELam M) E'' (T -o U)
| CSend : forall E E' T S M, check E M E' (TProd T (! T; S)) ->
                        check E (ECApp send M) E' S
| CRecv : forall E E' T S M, check E M E' (? T;S) ->
                        check E (ECApp receive M) E' (TProd T S)
| CFork : forall E E' S M, check E M E' ((TSession S) -o end!) ->
                      check E (ECApp fork M) E' (dual S)
| CWait : forall E E' M, check E M E' end? ->
                    check E (ECApp wait M) E' T1Nul
| CApp : forall E E' E'' M N T U, check E M E' (T -o U) ->
                             check E' N E'' T ->
                             check E (EApp M N) E'' U
| CPair: forall E E' E'' M N T U, check E M E' T ->
                             check E' N E'' U ->
                             check E (EPair M N) E'' (TProd T U)
| CInl : forall E E' M T U, check E M E' T ->
                       check E (EInl M) E' (TSum T U)
| CInr : forall E E' M T U, check E M E' U ->
                       check E (EInr M) E' (TSum T U)
| CLetPair : forall E E' E'' M N T T' U x y, lookup x E = Some T ->
                                        lookup y E = Some T' -> 
                                        check E M E' (TProd T T') ->
                                        check (insert 0 T (insert 0 T' E')) N E'' U ->
                                        check E (ELetPair x y M N) E'' U
| CCase : forall E E' E'' M N N' T T' U A, check E M E' (TSum T T') ->
                                      check (insert 0 T E')  N  E'' U /\ tl_error E'' = Some A ->
                                      check (insert 0 T' E') N'  E'' U /\ tl_error E'' = Some A ->
                                      check E (ECase M N N') E'' U
| CLetUnit: forall M N E E' E'' T, check E M E' T1Nul ->
                              check E' N E'' T ->
                              check E (ELetUnit M N) E'' T
| CNul : forall E, check E EUnit E T1Nul.

Hint Constructors check : check.

Example check_var : check nil (ELam (EVar 0)) nil (T1Nul -o T1Nul).
Proof. apply CLam with (E' := [None]). apply CVar. reflexivity. reflexivity. Qed.

Example check_lam_pair : forall A B, check nil (ELam (ELam (EPair (EVar 1) (EVar 0)))) nil (A -o B -o (TProd A B)).
Proof. intros.
       apply CLam with (E' := [None]); try reflexivity.
       apply CLam with (E' := [None; None]); try reflexivity.
       apply CPair with (E' := [Some B; None]).
       apply CVar. reflexivity.
       apply CVar. reflexivity.
Qed.

Lemma lift_EVar: forall w k x, lift w k (EVar x) = EVar (lift w k x).
Proof. intros. simpl_lift_goal. reflexivity. Qed.

Lemma subst_EVar: forall v k x, subst v k (EVar x) = subst_idx v k x.
Proof. intros. simpl_subst_goal. reflexivity. Qed.

Inductive red : term -> term -> Prop :=
| RUnit : forall M, red (ELetUnit () M) M
| RBeta : forall M V, value V ->
                 red (EApp (ELam M) V) (subst V 0 M)
| RLetSub : forall x y V V' M, value V ->
                          value V' ->
                          red (ELetPair x y (EPair V V') M) (subst V x (subst V' y M))
| RCApp: forall K M M', red M M' ->
                   red (ECApp K M) (ECApp K M')
| RVapp: forall V M M', value V ->
                   red M M' ->
                   red (EApp V M) (EApp V M')
| RLetUnit : forall M M' N, red M M' ->
                       red (ELetUnit M N) (ELetUnit M' N)
| RPair : forall M M' N, red M M' ->
                    red (EPair M N) (EPair M' N)
| RVPair : forall V M M', value V ->
                     red M M' ->
                     red (EPair V M) (EPair V M')
| RAbs : forall M M', red M M' ->
                 red (ELam M) (ELam M')
| RLetPair : forall x y M M' T, red M M' ->
                           red (ELetPair x y T M) (ELetPair x y T M')
| RInl : forall M M', red M M' ->
                 red (EInl M) (EInl M')
| RInr : forall M M', red M M' ->
                 red (EInr M) (EInr M')
| RCase : forall M M' N N', red M M' ->
                       red (ECase M N N') (ECase M' N N')
| RLeft : forall N N' V, value V ->
                    red (ECase (EInl V) N N') (subst V 0 N)
| RRight : forall N N' V, value V ->
                     red (ECase (EInr V) N N') (subst V 0 N').

Lemma unique: forall E E' M T U, check E M E' T -> check E M E' U -> T = U.
Proof. intros. induction H; simpl. inversion H0; subst. 
Abort.

(* Lemma substitution:
  forall E x t2 T1 T2,
  j (insert x T1 E) t2 T2 ->
  forall t1,
  j E t1 T1 ->
  j E (subst t1 x t2) T2.
 *)

Lemma substitution:
  forall (E: env type) (x : nat) (t2 : term) (T1 T2 : type),
    check (insert x T1 E) t2 (update x None E) T2 ->
    forall (t1  : term ), value t1 ->
          check E t1 (insert x T1 E) T1 ->
          check (insert x T1 E) (subst t1 x t2) (update x None E) T2.
Proof. intros.
       induction H; simpl_subst_goal;
         try solve [ econstructor; eauto; simpl].
       unfold subst_idx; dblib_by_cases; simpl. apply CVar; assumption.
       apply agree_below with (e2:= (update x0 None E0)) (k := x0)in H.

       Abort.

Theorem check_reduce : forall M M' E E' T, check E M E' T -> red M M' -> check E M' E' T.
Proof. induction M; intros.
       - inversion H0.
       - inversion H0; subst. inversion H; subst.
         * apply CSend with (T := T0). apply IHM; assumption.
         * apply CRecv. apply IHM; assumption.
         * apply CFork. apply IHM; assumption.
         * apply CWait. apply IHM; assumption.
       - inversion H0; inversion H; subst. apply IHM with (M' := M'0) in H5; try assumption.
         apply CLam with (E' := E'0); assumption.
       - inversion H; inversion H0; subst. 
         * inversion H11; subst. 

         * apply IHM2 with (M' := M'0) in H7; try assumption.
           apply CApp with (E' := E'0)(T := T0); assumption.
         destruct M'. inversion H0; subst. inversion H; inversion H0; subst.
      
(*
         Focus 2. apply CApp with (E' := E') (T := T).
         apply IHM1 with (M' := ) in H4
         apply IHM2 with (M' := ) in H7.
*)




(*  *)

