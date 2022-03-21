(** * Theory of Sets  EII-3 Coq functions
  Copyright INRIA (2016) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset2_aux.v,v 1.5 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset1 sset3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Infinity.
Definition nat_map := IM (fun n => J (Ro n)(Ro n.+1)).
Definition nat_fun := triple nat nat nat_map.


Lemma nat_map_P x:
  inc x (graph nat_fun) <-> exists n, x = J (Ro n) (Ro n.+1).
Proof.
by rewrite /nat_fun/nat_map; aw; split; [ move/IM_P | move => Î; apply/IM_P].
Qed.

Lemma nat_fun_function: function nat_fun.
Proof.
have cf: correspondence nat_fun.
  apply: corresp_create => x /IM_P [a ->].
  by apply /setXp_P; split; apply: R_inc.
have sf: source nat_fun = nat by rewrite /nat_fun; aw.
have tf: target nat_fun = nat by rewrite /nat_fun; aw.
split => //. 
  split; first by move => x /nat_map_P [n ->]; fprops.
  by move => x y /nat_map_P [n ->]/nat_map_P [m ->]; aw=> eq; rewrite(R_inj eq).
rewrite sf; set_extens t.
  move =>  [a <-]; apply/funI_P;exists (J (Ro a)(Ro a.+1)); aw; trivial.
  by apply/nat_map_P; exists a.
move/funI_P => [z /nat_map_P [a ->] ->]; aw; apply: R_inc.
Qed.

Lemma nat_fun_ev n: Vf nat_fun (Ro n) = (Ro n.+1).
Proof.
have rs: (inc (Ro n) (source nat_fun)).
   rewrite /nat_fun; aw; apply: R_inc.
move: (Vf_pr3 (nat_fun_function) rs) => /nat_map_P [u eql].
by rewrite (pr2_def eql) (R_inj (pr1_def eql)).
Qed.
  
Lemma nat_fun_injective: injection nat_fun.
Proof.
split; first by apply:nat_fun_function.
rewrite {1}/nat_fun; aw; move => x y [a <-] [b <-].
by rewrite ! nat_fun_ev => eq; rewrite (eq_add_S _ _ (R_inj eq)). 
Qed.
  

Lemma nat_fun_surjective: ~ surjection nat_fun.
Proof.
case; rewrite {2 3} /nat_fun; aw => _ H.
move: (H _ (R_inc 0)) => [x [n <-]].
by rewrite nat_fun_ev => eq; move:(R_inj eq).
Qed.

End Infinity.

(* Link between Bourbaki functions and Coq function; was a part of sset2.v
   but is not used anymore
*)


Module CoqFunctions.
(** We create a function from a map [f:a->b] *)

Definition gacreate (a b:Set) (f:a->b) := IM (fun y:a => J (Ro y) (Ro (f y))).
Definition acreate (a b:Set) (f:a->b)  := triple a b (gacreate f).

Lemma acreate_triple (a b:Set) (f:a->b): correspondence (acreate f).
Proof. 
apply: corresp_create => t /IM_P [v ->]; apply:setXp_i ; apply: R_inc.
Qed.

Lemma acreate_P (A B:Set) (f:A->B) x:
  inc x (graph (acreate f)) <-> exists u:A, x = J (Ro u) (Ro (f u)).
Proof. rewrite /acreate /gacreate; aw; apply/IM_P. Qed.

Lemma acreate_source (A B:Set) (f:A->B): source (acreate f) = A.
Proof. by rewrite /acreate; aw. Qed.

Lemma acreate_target (A B:Set) (f:A->B): target (acreate f) = B.
Proof. by rewrite /acreate; aw. Qed.

Hint Rewrite acreate_source acreate_target: aw.

Lemma acreate_function  (A B:Set) (f:A->B):
  function (acreate f).
Proof.
move: (acreate_triple f)=>cf; split=> //.
  split; fprops; move=> x y /acreate_P [v1 ->]/acreate_P [v2 ->]; aw=> eql.
  by rewrite (R_inj eql).
rewrite /acreate /gacreate /domain; aw.
set_extens t.
   move=> tA; apply/funI_P;exists (J t (Ro (f (Bo tA)))); last by aw.
   by apply /IM_P; exists (Bo tA); rewrite B_eq. 
move/funI_P => [x /IM_P [a ->] ->]; aw; trivial; apply: R_inc. 
Qed.

Hint Resolve acreate_function: fprops.

Lemma acreate_V  (A B:Set) (f:A->B) (x:A):
  Vf (acreate f)  (Ro x) =  Ro (f x).
Proof. 
have rs: (inc (Ro x) (source (acreate f))) by rewrite/acreate; aw; apply: R_inc.
move: (Vf_pr3 (acreate_function f) rs) => /acreate_P [u eql].
by rewrite (pr2_def eql) (R_inj (pr1_def eql)).
Qed.

(** We define [bcreate1 f] of type [source f-> target f]
 so that [ acreate (bcreate1 f) = f]  *)

Definition bcreate1 f (H:function f) :=
  fun x:source f => Bo (Vf_target H (R_inc x)). 

Lemma prop_bcreate1 f (H:function f) (x:source f):
  Ro (bcreate1 H x) = Vf f (Ro x) .
Proof. by apply: B_eq. Qed.

Lemma bcreate_inv1 f (H:function f):
  acreate (bcreate1 H) = f.
Proof.
apply: function_exten; fprops; rewrite {1}/acreate; aw; trivial.
by move=> x xs; rewrite - (B_eq xs) acreate_V; apply: prop_bcreate1.
Qed.


Fact Vf_mapping f A B x : source f = A  -> target f = B -> 
  function f -> inc x A -> inc (Vf f x) B.
Proof. move=> Ha Hb  ff; rewrite -Ha -Hb; fprops. Qed.


(** We define [bcreate f a b] of type [a->b],
it satisfies [ acreate (bcreate f a b) = f]  *)

Definition bcreate f A B 
  (H:function f)(Ha:source f = A)(Hb:target f = B):=
  fun x:A => Bo (Vf_mapping Ha Hb H (R_inc x)). 

Lemma prop_bcreate2 f A B 
  (H:function f) (Ha:source f = A)(Hb:target f = B)(x:A):
  Ro (bcreate H Ha Hb x) = Vf f (Ro x).
Proof. apply: B_eq. Qed.

Lemma bcreate_inv2 f A B
  (H:function f) (Ha:source f = A)(Hb:target f = B):
  acreate (bcreate H Ha Hb) = f.
Proof. 
apply: function_exten; fprops; rewrite /acreate; aw =>//.
by move=> x xs; rewrite -(B_eq xs) acreate_V; apply: prop_bcreate2.
Qed.

Lemma bcreate_inv3 (A B:Set) (f:A->B):
  bcreate (acreate_function f) (acreate_source f)(acreate_target f) =1 f.
Proof. by move=> a;apply: R_inj; rewrite prop_bcreate2 acreate_V. Qed.

Lemma bcreate_eq f (H:function f):
  bcreate1 H =1 bcreate H (refl_equal (source f)) (refl_equal (target f)).
Proof. by move=> a; apply: R_inj; rewrite prop_bcreate2 prop_bcreate1. Qed.


Definition empty_functionCt x := fun t:emptyset => match t return x with end.
Definition empty_functionC := empty_functionCt emptyset.


Definition identityC (a:Set): a->a := @id a.

Lemma identity_prop1 (a: Set) : acreate (@id  a) = identity a.
Proof. by apply: function_exten; fprops => t. Qed. 

Lemma identity_prop2 a:
  bcreate (identity_f a) (identity_s a) (identity_t a) =1 @id a.
Proof. 
by move=> x; apply: R_inj; rewrite prop_bcreate2 -identity_prop1 acreate_V. 
Qed.


(** Composition of Coq function *)

Lemma compositionC_A a b c d (f: c->d)(g:b->c)(h:a->b):
  (f \o g) \o h = f \o (g \o h).
Proof. done. Qed.

Lemma composeC_ev a b c (g:b->c) (f: a->b) x:
   (g \o f) x = g (f x).
Proof. done. Qed.

Lemma compose_id_leftC (a b:Set) (f:a->b):
  (@id b) \o f =1 f.
Proof. done. Qed.

Lemma compose_id_rightC (a b:Set) (f:a->b):
   f \o (@id a) =1 f.
Proof. done. Qed.


(** Function associated to set inclusion *)


Definition inclusionC x y (H: sub x y):=
  [fun u:x => Bo (H (Ro u) (R_inc u))].

Lemma inclusionC_pr x y (H: sub x y) (a:x):
  Ro(inclusionC H a) = Ro a.
Proof. by move => /=; apply: B_eq. Qed.


Lemma inclusionC_identity x:
  inclusionC (sub_refl (x:=x)) =1 @id x.
Proof. by move => v; apply: R_inj;rewrite inclusionC_pr. Qed.

Lemma inclusionC_compose x y z (Ha:sub x y)(Hb: sub y z):
  (inclusionC Hb) \o (inclusionC Ha) =1 inclusionC (sub_trans Ha Hb).
Proof. move=> t; by apply: R_inj; rewrite 3! inclusionC_pr. Qed.

(** Restriction of a Coq function; agreement of subsets *)

Definition restrictionC  (x a b:Set) (f:a->b)(H: sub x a) :=
  f \o (inclusionC H).

Definition agreeC (x a a' b b':Set) (f:a->b) (f':a'-> b')
  (Ha: sub x a)(Hb: sub x a') :=
  forall u:x, Ro(restrictionC f Ha u) = Ro(restrictionC f' Hb u).


Definition extendsC (a b a' b':Set) (g:a'->b')(f:a->b)(H: sub a a')  := 
  sub b b' /\ agreeC g f H (sub_refl (x:=a)).


Lemma extendsC_pr (a b a' b':Set) (g:a'->b')(f:a->b)(H: sub a a'):
  extendsC g f H -> forall x:a, Ro (f x) = Ro(g (inclusionC H x)).
Proof. 
move=> [e1]; rewrite /agreeC => eq x; rewrite eq. 
by rewrite /restrictionC composeC_ev inclusionC_identity.
Qed.


Lemma function_extends_restC (x a b:Set) (f:a->b)(H:sub x a):
  extendsC f (restrictionC f H) H.
Proof. 
split; fprops. 
move => t; rewrite /restrictionC compositionC_A 2! composeC_ev.
rewrite inclusionC_compose; congr (Ro (f _)).
by apply: R_inj; rewrite B_eq B_eq.
Qed.


Lemma agrees_same_restrictionC (a a' b x:Set)  (f:a->b)(g:a'->b)
  (Ha: sub x a)(Hb: sub x a'):
  agreeC f g Ha Hb -> restrictionC f Ha =1 restrictionC g Hb.
Proof. move => ag z; apply: R_inj; apply: ag. Qed.


Definition restriction2C (a a' b b':Set) (f:a->b)(Ha:sub a' a)
  (H: forall u:a', inc (Ro (f (inclusionC Ha u))) b') := 
  fun u=> Bo (H u).

Lemma restriction2C_pr (a a' b b':Set) (f:a->b)(Ha:sub a' a)
  (H: forall u:a', inc (Ro (f (inclusionC Ha u))) b') (x:a'):
  Ro (restriction2C  H x) = Vf (acreate f) (Ro x).
Proof. 
rewrite /restriction2C B_eq; set (y:=inclusionC Ha x).  
have RR: (Ro y = Ro x) by rewrite /y/inclusionC B_eq. 
by rewrite -RR acreate_V.
Qed.

Lemma restriction2C_pr1 (a a' b b':Set) (f:a->b)
  (Ha:sub a' a)(Hb:sub b' b)
  (H: forall u:a', inc (Ro (f (inclusionC Ha u))) b'):
   f \o (inclusionC Ha) =1  (inclusionC Hb) \o (restriction2C H).
Proof. 
by move=>  t; rewrite /restriction2C; apply: R_inj; rewrite B_eq B_eq.
Qed.




Lemma acreate_exten  (a b: Set) (f g: a-> b):
  f =1 g -> acreate f = acreate g.
Proof.
move=> h; apply: function_exten; aww.
by move=> x [z za]; rewrite -za ! acreate_V h.
Qed.


Lemma composable_acreate (a b c:Set) (f: a-> b)(g: b->c):
  (acreate g) \coP (acreate f).
Proof. rewrite/composable; aw; split;fprops.  Qed.

Lemma compose_acreate (a b c:Set) (g: b->c)(f: a-> b):
  (acreate g) \co (acreate f) = acreate (g \o f).
Proof.
have cfg:= (composable_acreate f g).
apply: function_exten; try fct_tac; aww.
by move=> x xa /=; rewrite compfV//; aw; trivial; rewrite -(B_eq xa)  3! acreate_V.  
Qed.

(* --- *)



(** Bijectivity of Coq functions  *)

Definition injectiveC (a b:Set) (f:a->b) := forall u v, f u = f v -> u =v.
Definition surjectiveC (a b:Set) (f:a->b) := forall u, exists v, f v = u.
Definition bijectiveC (a b:Set) (f:a->b) := injectiveC f /\ surjectiveC f.
Definition right_inverseC (a b:Set) (f: a->b)  (H:surjectiveC f) (v:b) :=
   (chooseT (fun k:a => f k = v) 
     match H v with | ex_intro x _ => inhabits x end).
Definition inverseC  (a b:Set) (f: a->b) (H:bijectiveC f) 
   := right_inverseC (proj2 H).

Lemma bijectiveC_pr (a b:Set) (f:a->b) (y:b):
  bijectiveC f -> exists! x:a, f x =y.
Proof.
move=> [fi fs]; apply /unique_existence; split; first by apply: fs.
by move=> x x' <- veq; symmetry; apply: fi.
Qed.

Lemma identityC_fb (x:Set): bijectiveC (@id x).
Proof. by split => // u; exists u. Qed.


Lemma composeC_inj (a b c:Set) (f:a->b)(f':b->c):
  injectiveC f-> injectiveC f' -> injectiveC (f' \o f).
Proof. by move=> fi fi' x y p; apply: fi; apply: fi'. 
Qed.

Lemma composeC_surj (a b c:Set) (f:a->b)(f':b->c):
  surjectiveC f -> surjectiveC f' -> surjectiveC (f' \o f).
Proof.
move => sf sf' y; move: (sf' y) => [w <-]; move: (sf w) => [z <-].
by exists z.
Qed.

Lemma composeC_bij (a b c:Set) (f:a->b)(f':b->c):
  bijectiveC f -> bijectiveC f' -> bijectiveC (f' \o f).
Proof. 
move=> [fi fs] [fi' fs']. 
by split; [apply: composeC_inj| apply: composeC_surj ].
Qed.

Lemma right_inverse_pr (a b:Set) (f: a->b) (H:surjectiveC f) (x:b):
  f (right_inverseC H x) = x.
Proof. 
by rewrite /right_inverseC; apply:(chooseT_pr (p:= fun k : a => f k = x)). 
Qed.



Section InverseProps.
Variables (A B: Set) (f: A -> B).
Hypothesis (H:bijectiveC f). 

Lemma inverseC_prb (x: B): f ((inverseC H) x) = x.
Proof.  apply:(right_inverse_pr (proj2 H)).  Qed.
 
Lemma inverseC_pra (x: A):  (inverseC H) (f x) = x.
Proof. exact: (proj1 H _ _  (inverseC_prb (f x))). Qed.

Lemma bij_left_inverseC: (inverseC H) \o f =1 @id A. 
Proof. by move=> w; rewrite composeC_ev inverseC_pra.  Qed.

Lemma bij_right_inverseC: f \o (inverseC H) =1 @id B. 
Proof. by move=> t;rewrite composeC_ev inverseC_prb. Qed.

Lemma bijective_inverseC:  bijectiveC (inverseC H).
Proof. 
split.  
  by move=> x y sv; rewrite -(inverseC_prb x) -(inverseC_prb y) sv.
by move=> u; exists (f u); rewrite inverseC_pra. 
Qed.
End InverseProps.


Lemma bijection_coq (a b: Set) (f:a->b):
  bijective f <-> bijectiveC f.
Proof.
split.
   move => [g ga gb]; split.
     by move=> x x' /(congr1 g); rewrite 2! ga. 
   by move=> x; exists (g x). 
move => H; exists (inverseC H).
  apply: bij_left_inverseC.
apply: bij_right_inverseC.
Qed.

Lemma inverse_fun_involutiveC (a b:Set) (f:a->b) (H: bijectiveC f):
  f =1 inverseC(bijective_inverseC H).
Proof. 
move=> x;move: (bijective_inverseC H) => [i s]; apply: (i).
by rewrite inverseC_pra inverseC_prb.
Qed.

Lemma bcreate_fi f a b
  (H:function f)(Ha:source f = a)(Hb:target f = b):
  injection f -> injectiveC (bcreate H Ha Hb).
Proof.
move=> [ff fi] x y eql; apply: R_inj; apply: fi.
- by rewrite Ha; apply: R_inc. 
- by rewrite Ha; apply: R_inc. 
- by move: (f_equal (@Ro b) eql); rewrite 2! prop_bcreate2. 
Qed.

Lemma bcreate_fs f a b
  (H:function f)(Ha:source f = a)(Hb:target f = b):
  surjection f -> surjectiveC (bcreate H Ha Hb).
Proof. 
move=> [ff sf] u.
have Rt: (inc (Ro u) (target f)) by rewrite Hb; apply: R_inc.
have [x xs xv] := (sf _ Rt).
rewrite Ha in xs; exists (Bo xs). 
by apply: R_inj; rewrite xv prop_bcreate2 B_eq.
Qed.

Lemma bcreate_fb f a b
  (H:function f)(Ha:source f =a)(Hb:target f =b):
  bijection f -> bijectiveC (bcreate H Ha Hb).
Proof. 
by move=> [fi fs];split ; [apply: bcreate_fi | apply: bcreate_fs].
Qed.

Lemma bcreate1_fi f (H:function f):
  injection f -> injectiveC (bcreate1 H).
Proof. 
by move=> fi x y; rewrite !(bcreate_eq H); apply: bcreate_fi. 
Qed.

Lemma bcreate1_fs f (H:function f):
  surjection f -> surjectiveC (bcreate1 H).
Proof.  
move=> sf x. 
move: (bcreate_fs H (refl_equal (source f)) (refl_equal (target f)) sf x). 
by move => [v xsf]; exists v; rewrite -xsf  -(bcreate_eq H). 
Qed.

Lemma bcreate1_fb f (H:function f):
  bijection f -> bijectiveC (bcreate1 H).
Proof. 
by move=> [p1 p2];split; [ apply: bcreate1_fi | apply: bcreate1_fs]. 
Qed.

Lemma acreate_fi (a b:Set) (f:a->b):
  injectiveC f -> injection (acreate f).
Proof.
move=> fi; split; first by fprops.
move=> x y; rewrite {1 2} /acreate; aw => xa ya.
rewrite -(B_eq xa) - (B_eq ya) (acreate_V f (Bo xa)) (acreate_V f (Bo ya)). 
by move=> eq; move: (R_inj eq)=> eqv; rewrite (fi  _ _ eqv). 
Qed.

Lemma acreate_fs (a b:Set) (f:a->b):
  surjectiveC f -> surjection (acreate f).
Proof.
move=> sf; split; fprops.
aw; move => y yb; move: (sf (Bo yb)) => [v fv].
by exists (Ro v); [by apply: R_inc | rewrite acreate_V fv  B_eq]. 
Qed.

Lemma acreate_fb (a b:Set) (f:a->b):
  bijectiveC f -> bijection (acreate f).
Proof. 
by move=> [i j]; split; [ apply: acreate_fi| apply: acreate_fs].
Qed.

(* Typechecking says that [r:b->a] and [s:b->a] *)

Definition is_left_inverseC (a b:Set) (f:a->b) r := r \o f =1 @id a.
Definition is_right_inverseC (a b:Set) (f:a->b) s:= f \o s =1 @id b.


Lemma right_i_v (a b:Set)  (f:a->b) s (x:b): 
  is_right_inverseC f s ->  f (s x) = x.
Proof. by move=> e; move: (e x); rewrite composeC_ev. Qed.

Lemma left_i_v (a b:Set) (f:a->b) r (x:a):
  is_left_inverseC f r -> r (f x) = x.
Proof.  by move=> e; move: (e x); rewrite composeC_ev. Qed.


Lemma inj_if_exists_left_invC (a b:Set) (f:a-> b):
  (exists r, is_left_inverseC f r) -> injectiveC f.
Proof.
move=> [r ilr] x x'.
by move /(congr1 r); move: (ilr x) (ilr x')  => /= -> ->.
Qed.

Lemma surj_if_exists_right_invC (a b:Set) (f:a->b):
  (exists s, is_right_inverseC f s) -> surjectiveC f.
Proof. 
by move=> [s rsf] u; exists (s u); rewrite (right_i_v u rsf).
Qed.


Definition left_inverseC (a b:Set) (f: a->b)(H:inhabited a) 
  (v:b) := (chooseT (fun u:a => (~ (exists x:a, f x = v)) \/ (f u = v)) H).

Lemma left_inverseC_pr (a b:Set) (f: a->b) (H:inhabited a) (u:a):
  f (left_inverseC f H (f u)) = f u.
Proof.
rewrite /left_inverseC.
set p:= fun u:a => _.
have: (p (chooseT p H)) by apply: chooseT_pr; exists u; right.
by case=>//; case; exists u.  
Qed.
 
Lemma left_inverse_comp_id  (a b:Set) (f:a->b)  (H:inhabited a):
  injectiveC f -> (left_inverseC f H) \o f =1 @id a.
Proof. 
move => fi t; apply fi; rewrite composeC_ev;apply: left_inverseC_pr.
Qed.

Lemma exists_left_inv_from_injC (a b:Set) (f:a->b): inhabited a ->
  injectiveC f -> exists r, is_left_inverseC f r.
Proof.
by move=> H fi; exists (left_inverseC f H); apply: left_inverse_comp_id.
Qed.

Lemma right_inverse_comp_id (a b:Set) (f:a-> b) (H:surjectiveC f):
  f \o (right_inverseC H)  =1 @id b.
Proof. move=> x; rewrite composeC_ev;apply: right_inverse_pr. Qed.

Lemma exists_right_inv_from_surjC (a b:Set)(f:a-> b) (H:surjectiveC f):
  exists s, is_right_inverseC f s.
Proof. exists (right_inverseC H); apply: right_inverse_comp_id. Qed.




Lemma inclusionC_fi a b (H: sub a b):
  injectiveC (inclusionC H).
Proof. 
move => x y si; apply: R_inj.
by rewrite - (inclusionC_pr H x) si (inclusionC_pr H y).
Qed.


Lemma inverseC_prc (a b:Set) (f:a-> b) (H:bijectiveC f):
  inverse_fun (acreate f) = acreate(inverseC H).
Proof. 
move: (acreate_fb H) => ab.
apply: function_exten.
- by apply: bijective_inv_f.
- by fprops.
- by rewrite/acreate; aw. 
- by rewrite/acreate; aw. 
move => x; aw => xb.
have [y eq]: exists y:a, f y = (Bo xb) by apply: (proj2 H).
set g :=  (acreate (inverseC H)).
have ta: a = target (acreate (inverseC H)) by rewrite acreate_target.
set u := Vf g x.
have: x = Vf (acreate f) u.
  by rewrite /u - {2} (B_eq xb) - eq acreate_V inverseC_pra acreate_V eq B_eq.
move => h; symmetry;apply: Vf_pr; first by apply: bijective_inv_f.
rewrite /inverse_fun; aw; apply /igraph_pP; rewrite h; apply: Vf_pr3 => //.
  fct_tac.
aw; rewrite /u ta; apply: Vf_target; first by apply: acreate_function.
by rewrite acreate_source.
Qed.

Lemma bijective_double_inverseC (a b:Set) (f:a->b) g g':
  g \o f =1 @id a -> f \o g' =1 @id b ->
  bijectiveC f.
Proof. 
move=> c1 c2; split.
  move=> x x' /(congr1 g); rewrite -!(composeC_ev g f) !c1 //.
move=> x; exists (g' x); rewrite -!(composeC_ev f g') c2 //.
Qed.

Lemma bijective_double_inverseC1 (a b:Set) (f:a->b) g g'
  (Ha: g \o f =1 @id a)(Hb: f \o g' =1 @id b)
  (h := inverseC (bijective_double_inverseC Ha Hb)):
  g =1 h /\ g' =1 h.
Proof. 
have sg: (g' =1 g). 
  by move=> x; rewrite -{1} (Ha (g' x)) -{2} (Hb x) !composeC_ev.
suff gh: (g' =1 h) by split =>//; apply: ftrans gh.
by move => x; rewrite /h - {2} (Hb x) inverseC_pra.
Qed.


Lemma right_inverse_from_leftC (a b:Set) (r:b->a)(f:a->b):
  is_left_inverseC f r -> is_right_inverseC r f.
Proof. trivial. Qed.

Lemma left_inverse_from_rightC (a b:Set) (s:b->a)(f:a->b):
  is_right_inverseC f s -> is_left_inverseC s f.
Proof. trivial. Qed.

Lemma left_inverse_surjectiveC (a b:Set) (r:b->a)(f:a->b):
  is_left_inverseC f r -> surjectiveC r.
Proof. by move=> h; apply: surj_if_exists_right_invC; exists f. Qed.

Lemma right_inverse_injectiveC (a b:Set) (s:b->a)(f:a->b):
  is_right_inverseC f s -> injectiveC s.
Proof. move=> h; apply: inj_if_exists_left_invC; by exists f. Qed.

Lemma section_uniqueC (a b:Set) (f:a->b)(s:b->a)(s':b->a):
  is_right_inverseC f s -> is_right_inverseC f s' ->
  (forall x:a, (exists u:b, x = s u) = (exists u':b, x = s' u')) ->
  s =1 s'.
Proof. 
move=>  r1 r2 sp x.
have [u' eql]:  (exists u' : b, s x = s' u') by rewrite- (sp (s x)); exists x. 
move: (f_equal f eql); rewrite (right_i_v x r1) (right_i_v u' r2).
by rewrite eql; move=>->. 
Qed.


Lemma left_inverse_composeC (a b c:Set) 
  (f:a->b) (f':b->c)(r:b->a)(r':c->b):
  is_left_inverseC  f' r' -> is_left_inverseC f r ->
  is_left_inverseC  (f' \o f) (r \o r').
Proof. 
by move=> le' le x;rewrite !composeC_ev (left_i_v (f x) le') (left_i_v x le). 
Qed.

Lemma right_inverse_composeC  (a b c:Set) 
  (f:a->b) (f':b->c)(s:b->a)(s':c->b):
  is_right_inverseC f' s' -> is_right_inverseC f s ->
  is_right_inverseC (f' \o f) (s \o s') .
Proof. 
by move=> H H' x ;rewrite !composeC_ev (right_i_v (s' x) H') (right_i_v x H).
Qed.

Lemma inj_right_composeC (a b c:Set) (f:a->b) (f':b->c):
  injectiveC (f' \o f) -> injectiveC f.
Proof. by move=> ci x y sv; apply: ci; rewrite !composeC_ev sv. Qed.

Lemma surj_left_composeCl (a b c:Set) (f:a->b) (f':b->c):
  surjectiveC (f' \o f) -> surjectiveC f'.
Proof.
by move=> sc x; move: (sc x)=> [y <-]; exists (f y). Qed.

Lemma surj_left_compose2C (a b c:Set) (f:a->b) (f':b->c):
  surjectiveC (f' \o f) -> injectiveC f' -> surjectiveC f.
Proof.
by move => sc if' x; move: (sc (f' x)) => [y sv];  exists y; apply: if'.
Qed.

Lemma inj_left_compose2C (a b c:Set) (f:a->b) (f':b->c):
  injectiveC (f' \o f) -> surjectiveC f -> injectiveC f'.
Proof. 
move=> ic sf x x' sv.
move: (sf x) (sf x') => [y yv] [y' y'v].
have: (y = y') by apply: ic; rewrite !composeC_ev yv y'v sv.
by rewrite -yv -y'v; move=>->. 
Qed.

Lemma left_inv_compose_rfC (a b c:Set) (f:a->b) (f':b->c)(r'': c->a):
  is_left_inverseC (f' \o f) r'' -> 
  is_left_inverseC f (r'' \o f') .
Proof. by move=> li x; apply: (left_i_v x li). Qed.

Lemma right_inv_compose_rfC (a b c:Set) (f:a->b) (f':b->c)(s'': c->a):
  is_right_inverseC  (f' \o f) s'' -> 
  is_right_inverseC f' (f \o s'').
Proof. move=> ri x; by apply: (right_i_v x ri).  Qed.

Lemma left_inv_compose_rf2C (a b c:Set) (f:a->b) (f':b->c)(r'': c->a):
  is_left_inverseC (f' \o f) r'' -> surjectiveC f ->
  is_left_inverseC f' (f \o r'').
Proof. move=> li s t;move: (s t) => [v <-]; exact: (f_equal f (li v)).  Qed. 

Lemma right_inv_compose_rf2C (a b c:Set) (f:a->b) (f':b->c)(s'': c->a):
  is_right_inverseC (f' \o f) s'' -> injectiveC f'->
  is_right_inverseC f (s'' \o f').
Proof. move=> ri inj;move=> t; apply: inj; exact (ri (f' t)). Qed. 



Lemma exists_left_composableC (a b c:Set) (f:a->b)(g:a->c):
  surjectiveC g ->
  ((exists h, h \o g =1 f) <->
    (forall (x y:a), g x = g y -> f x = f y)).
Proof. 
move=> sg; split. 
  by move=> [h hp] x y; move: (hp x) (hp y) => /= <- <- <-. 
move: (exists_right_inv_from_surjC sg) => [h hp] hyp.
by exists (f \o h) => t /=; apply: hyp; move:(hp (g t)). 
Qed.


Lemma exists_left_composable_auxC (a b c:Set) (f:a->b) (g:a-> c) s h:
   is_right_inverseC g s ->
  h \o g =1 f -> h =1 f \o s.
Proof. 
by move=> ri eq x /=; rewrite -eq /=;  move: (ri  x) => /=  ->.
Qed.



Lemma exists_unique_left_composableC (a b c:Set) (f:a->b)(g:a->c) h h':
  surjectiveC g -> h \o g =1 f -> h' \o g =1 f ->  h =1 h'.
Proof. 
move=> sg chg chg' x.
move: (exists_right_inv_from_surjC sg) => [j jp].
rewrite (exists_left_composable_auxC jp chg).
by rewrite (exists_left_composable_auxC jp chg').
Qed.


Lemma left_composable_valueC (a b c:Set) (f:a->b)(g:a->c) s h:
  surjectiveC g ->  (forall (x y:a), g x = g y -> f x = f y) ->
  is_right_inverseC g s  ->  h =1 f \o s -> 
  h \o g =1 f.
Proof.
move=> sg hyp rish eq x /=. 
by rewrite eq /=; apply: hyp; rewrite -{2} (rish (g x)).
Qed.


Lemma exists_right_composable_auxC (a b c:Set) (f:a->b) (g:c->b) h r:
  is_left_inverseC g r  -> g \o h =1 f
  -> h =1 r \o f.
Proof. move=> li eq x /=; rewrite -(eq x); symmetry;exact: (li (h x)). Qed.


Lemma exists_right_composable_uniqueC (a b c:Set)(f:a->b) (g:c->b) h h':
  injectiveC g -> g \o h =1 f -> g \o h' =1 f -> h =1 h'.
Proof.
move=> ig c1 c2 x; apply: ig; by move: (c1 x)(c2 x) => /= -> ->.
Qed.


Lemma exists_right_composableC (a b c:Set) (f:a->b) (g:c->b):
  injectiveC g ->
  ((exists h, g \o h =1 f) <-> (forall u, exists v, g v = f u)).
Proof.
move=>  ig; split.
  by move=> [h cgh] u; exists (h u); rewrite -cgh. 
move => mh.
case: (emptyset_dichot c) => hyp.
  have ae: (a = emptyset). 
    apply /set0_P => y ya. 
    by move: (mh (Bo ya)) => [x _]; rewrite hyp in x; case: x.  
  symmetry in hyp; symmetry in ae. 
  have [pa pb pc]:= empty_function_function.
  rewrite ae in pb; rewrite hyp in pc.
  exists (bcreate pa pb pc) => v.
  elimtype False; rewrite -ae in v; case: v.
have [x [xc _]]:= hyp.
move: (exists_left_inv_from_injC (inhabits xc) ig) => [r rv].
exists (r \o f). 
move=> y /=;  move: (mh y)=> [v <-];  exact (f_equal g (rv v)). 
Qed.


Lemma right_composable_valueC (a b c:Set) (f:a->b) (g:c->b) r h:
  injectiveC g -> is_left_inverseC r g -> (forall u, exists v, g v = f u) ->
  h =1 r \o f ->  g \o h =1 f.
Proof. 
move=> ig lir hyp eq x /=; rewrite eq /=.
by move: (hyp x)=> [v <-]; rewrite (left_i_v). 
Qed.


Lemma ext_to_prod_propP a a' (x: a \times a'):  inc (P (Ro x)) a.
Proof. 
have: (inc (Ro x) (a \times a')) by apply: R_inc.
by move/setX_P => [_].
Qed.

Lemma ext_to_prod_propQ a a' (x:  a \times a'):  inc (Q (Ro x)) a'.
Proof. 
have: (inc (Ro x) (a \times a')) by apply: R_inc.
by move/setX_P => [_].
Qed.

Lemma ext_to_prod_propJ (b b':Set) (x:b)(x':b'):
  inc (J (Ro x)(Ro x'))  (b \times b').
Proof. apply/setXp_i;apply: R_inc. Qed.
  
Definition pr1C a b:= fun x: a \times b => Bo(ext_to_prod_propP x).
Definition pr2C a b:= fun x: a \times b => Bo(ext_to_prod_propQ x).
Definition pairC (a b:Set) := fun (x:a)(y:b) => Bo(ext_to_prod_propJ x y).

Definition ext_to_prodC (a b a' b':Set) (u:a->a')(v:b->b') :=
  fun x => pairC (u (pr1C x)) (v (pr2C x)).

Lemma prC_prop (a b:Set) (x: a \times  b):
  Ro x = J (Ro (pr1C x)) (Ro (pr2C x)).
Proof. 
have: (inc (Ro x) (a \times b)) by apply: R_inc. 
by rewrite /pr1C/pr2C B_eq B_eq; move/setX_P=> [-> _].
Qed.

Lemma pr1C_prop (a b:Set) (x:a \times b):
  Ro (pr1C x) = P (Ro x). 
Proof. by rewrite (prC_prop x); aw. Qed.

Lemma pr2C_prop (a b:Set) (x:a \times b):
  Ro (pr2C x) = Q (Ro x). 
Proof. by rewrite (prC_prop x); aw. Qed.

Lemma prJ_prop (a b:Set) (x:a)(y:b):
  Ro(pairC x y) = J (Ro x) (Ro y).
Proof. by rewrite /pairC  B_eq. Qed.

Lemma prJ_recov (a b:Set) (x:a \times b):
  pairC (pr1C x) (pr2C x) = x.
Proof. 
apply: R_inj; rewrite prJ_prop pr1C_prop pr2C_prop. 
rewrite (setX_pair (A:=a)(B:=b)) //; by apply: R_inc.
Qed.

Lemma ext_to_prod_prop (a b a' b':Set) (u:a->a')(v:b->b') (x:a)(x':b):
  J(Ro (u x)) (Ro (v x')) = Ro(ext_to_prodC u v (pairC x x')).
Proof. 
rewrite /ext_to_prodC prJ_prop.
have <-: (x =  (pr1C (pairC x x'))). 
  by apply: R_inj; rewrite pr1C_prop  prJ_prop; aw. 
have <- //: (x' =  (pr2C (pairC x x'))). 
  by apply: R_inj; rewrite pr2C_prop  prJ_prop; aw. 
Qed.


Lemma injective_ext_to_prod2C (a b a' b':Set) (u:a->a')(v:b->b'):
  injectiveC u -> injectiveC v -> injectiveC (ext_to_prodC u v).
Proof. 
move=> iu iv x x' / (congr1 (@Ro (product a' b'))).
rewrite -(prJ_recov x) -(prJ_recov x').
rewrite - 2!ext_to_prod_prop; move=> eql.
by rewrite (iu _ _ (R_inj (pr1_def eql))) (iv _ _ (R_inj (pr2_def eql))). 
Qed.

Lemma surjective_ext_to_prod2C (a b a' b':Set) (u:a->a')(v:b->b'):
  surjectiveC u -> surjectiveC  v-> surjectiveC (ext_to_prodC u v).
Proof. 
move=> su sv x; rewrite -(prJ_recov x).
have pRx: pairp (Ro x) by case /setX_P: (R_inc x). 
  move: (su (pr1C x)) => [y yp]; move: (sv (pr2C x)) => [y' y'p].
exists (pairC y y'); apply: R_inj. 
by rewrite - ext_to_prod_prop yp y'p prJ_recov pr1C_prop pr2C_prop; aw.
Qed.

Lemma bijective_ext_to_prod2C (a b a' b':Set) (u:a->a')(v:b->b'):
  bijectiveC u -> bijectiveC v -> bijectiveC (ext_to_prodC u v).
Proof. 
rewrite /bijectiveC; move=> [p1 p2][p3 P4].
by split ; [apply: injective_ext_to_prod2C | apply: surjective_ext_to_prod2C].
Qed.

Lemma compose_ext_to_prod2C (a b c a' b' c':Set) (u:b-> c)(v:a->b)
  (u':b'-> c')(v':a'->b'):
  (ext_to_prodC u u') \o (ext_to_prodC v v') =1
  ext_to_prodC (u \o v)(u' \o v').
Proof.  
move => x /=; rewrite -(prJ_recov x). 
move: (ext_to_prod_prop v v' (pr1C x) (pr2C x));rewrite -prJ_prop=> xx.
rewrite - (R_inj xx).
by apply: R_inj; rewrite  -2! ext_to_prod_prop. 
Qed.

Lemma inverse_ext_to_prod2C (a b a' b':Set) (u:a->a')(v:b->b')
  (Hu: bijectiveC u)(Hv:bijectiveC  v):
  inverseC (bijective_ext_to_prod2C Hu Hv) =1
  ext_to_prodC (inverseC Hu)(inverseC Hv).
Proof. 
move => x.
suff ww: x = ext_to_prodC u v (ext_to_prodC (inverseC Hu) (inverseC Hv) x).
  by rewrite  ww inverseC_pra -ww.
move: (compose_ext_to_prod2C u (inverseC Hu) v (inverseC Hv))=> eq.
move: (eq x) => /= ->.
rewrite - (prJ_recov x); apply: R_inj.
by rewrite -ext_to_prod_prop /= inverseC_prb  inverseC_prb prJ_prop.
Qed.


Definition imageC (a b:Set) (f:a->b) := IM (fun u:a => Ro (f u)).

Lemma imageC_inc (a b:Set) (f:a->b) (x:a): inc (Ro (f x)) (imageC f).
Proof. by rewrite /imageC; apply /IM_P; exists x. Qed.

Lemma imageC_exists (a b:Set) (f:a->b) x:
  inc x (imageC f) -> exists y:a,  x = Ro (f y).
Proof. by rewrite /imageC=> /IM_P [y] ->; exists y. Qed.

Lemma sub_image_targetC (a b:Set) (f:a->b): sub (imageC f) b.
Proof. by move=> x  /(imageC_exists) [y] ->;  apply: R_inc. Qed.

Definition restriction_to_imageC (a b:Set) (f:a->b) :=
  fun x:a => Bo (imageC_inc f x).

Lemma restriction_to_imageC_pr (a b:Set) (f:a->b) (x:a):
  Ro (restriction_to_imageC f x) = Ro (f x).
Proof. by rewrite /restriction_to_imageC  B_eq. Qed.

Lemma canonical_decomposition1C (a b:Set) (f:a->b)
  (g:a-> imageC f)(i:imageC f ->b):
  g = restriction_to_imageC f ->
  i = inclusionC (sub_image_targetC (f:=f))  ->
  [/\ injectiveC i , surjectiveC g &
  (injectiveC f -> bijectiveC g)].
Proof. 
move=>  gv iv.  
have sg: surjectiveC g.
  move=> x; rewrite gv.  
  have aux: (inc (Ro x) (imageC f)) by apply: R_inc.
  move: (imageC_exists aux)=> [y]; exists y; apply: R_inj.
  by rewrite restriction_to_imageC_pr; symmetry. 
split => //.
  move=> x x' eq;  move: (f_equal (@Ro b) eq). 
  by rewrite iv  2! inclusionC_pr;  apply: R_inj.
move=> fi; split=> //; move=> x y eq ; move: (f_equal (@Ro (imageC f)) eq). 
rewrite gv 2!restriction_to_imageC_pr=> eqbis.
by apply: fi;  apply: R_inj.
Qed.

(* from sset3  *)

Definition constantp x y (f: x-> y) := forall a b, f a = f b.


Lemma setIt_i (I:Set) (f:I-> Set) x: nonempty I ->
  (forall j, inc x (f j)) -> inc x (intersectiont f). 
Proof. by move=> pa pb; apply/setIt_P. Qed.

Lemma setIt_hi (I:Set) (f:I-> Set) x j:
  inc x (intersectiont f) -> inc x (f j).
Proof.
have neJ: nonempty I by exists (Ro j); exists j.
move /(setIt_P _ neJ); apply. 
Qed.



Lemma setUt_exten (I:Set)  (f: I-> Set) (f':I->Set):
  f =1 f' -> uniont f = uniont f'.
Proof.
move=> hyp; set_extens t; move/setUt_P=> [z zi]; apply/setUt_P; exists z.
  by rewrite -hyp. 
by rewrite hyp.
Qed.


Lemma setIt_0 (I:Set) (f:I-> Set):
  I = emptyset -> intersectiont f = emptyset.
Proof. 
move=>  ie; apply /set0_P => t /Zo_S /setUt_P [i ii].
by move:(R_inc i);  rewrite {2} ie => /in_set0.
Qed.

Lemma setIt_exten (I:Set) (f f':I-> Set):
   f =1 f' -> (intersectiont f) = (intersectiont f').
Proof.
move=> hyp; case: (emptyset_dichot I) => ie.
  by rewrite !(setIt_0 _ ie).
set_extens t; move/(setIt_P _ ie) => h; apply/(setIt_P _ ie) => j. 
  rewrite - hyp; apply: h.
rewrite hyp; apply: h.
Qed.

Lemma setUt_s1 (I:Set) (f: I-> Set) i:  sub (f i) (uniont f).
Proof. by move=> t tf; apply/ setUt_P; exists i. Qed.

Lemma setIt_s1 (I:Set) (f: I-> Set) i:  sub (intersectiont f) (f i). 
Proof. move=> t; apply: setIt_hi. Qed.


Lemma setUt_s2 (I:Set) (f: I-> Set) x:
  (forall i, sub (f i) x) ->  sub (uniont f) x.
Proof. by move=> hyp t /setUt_P [z tfz]; apply: (hyp z). Qed.

Lemma setIt_s2 (I:Set)  (f: I-> Set) x:
  nonempty I ->
  (forall i, sub x (f i)) ->  sub x (intersectiont f).
Proof. by move=> ne hyp t tx; apply/setIt_P => // j; apply: hyp. Qed.

Lemma setIt_sub2 (I:Set) (f: I-> Set) x:
  (forall i, sub (f i) x) ->  sub (intersectiont f)  x.
Proof. 
move=> hyp t ti.
case: (emptyset_dichot I) => ie.
  by move: ti; rewrite setIt_0 // => /in_set0. 
case: ie => y [ z _]; exact:(hyp z _ (setIt_s1 z ti)).
Qed.


Lemma setUt_sub2 (I:Set) (f: I-> Set) x:
  nonempty I -> (forall i, sub x (f i)) -> sub x (uniont f).
Proof. by move=> [y yI] hyp t tx; apply/setUt_P; exists (Bo yI);apply: hyp. Qed.


Theorem setUt_rewrite (I K:Set) (f: K->I) (g:I ->Set):
  (forall u, exists v, f v = u) ->
  uniont g = uniont (g \o f).
Proof.
move=> sf; set_extens t; move/setUt_P=> [z zp]; apply/setUt_P.
  by move: (sf z) => [v fv] /=; exists v; ue.
by exists (f z).
Qed.

Theorem setIt_rewrite (I K:Set) (f: K->I) (g:I ->Set):
  (forall u, exists v, f v = u) ->
  intersectiont g  = intersectiont (g \o f).
Proof. 
move=> sf; case: (emptyset_dichot I) => ei.
  rewrite ! setIt_0 =>//; apply /set0_P => y [x _].
  move: (f x); rewrite ei; case.
have nek: nonempty K.
  move: ei => [k [i]] _; move: (sf i)=> [j _]; exists (Ro j); apply: R_inc.
set_extens t; move/setIt_P=> h; apply/setIt_P => // j; first by apply: (h ei).
move: (sf j) => [k <-]; exact: (h nek k).
Qed.


Lemma setUt_constant (I:Set) (f:I ->Set) (x:I):
  constantp f -> uniont f = f x.
Proof.
move=> cf; set_extens t; first by move/setUt_P => [z]; rewrite (cf x z).
by move=> tp;  apply/setUt_P; exists x.
Qed.

Lemma setIt_constant (I:Set) (f:I ->Set) (x:I):
  constantp f -> intersectiont f = f x.
Proof.
have neI: nonempty I by exists (Ro x); apply: R_inc.
move => cf;apply: extensionality; first by apply:setIt_s1.
by move => z j;apply: setIt_i => // k; rewrite (cf k x). 
Qed.


Lemma setUt_1 (a:Set) (x:a) (f: singleton (Ro x) -> Set):
  uniont f = f (Bo (set1_1 (Ro x))).
Proof. 
set_extens t => pt; last by  apply/setUt_P; exists (Bo (set1_1 (Ro x))).
move /setUt_P: pt => [y tfy].  
have <- //: (y = (Bo (set1_1 (Ro x)))).
by apply: R_inj; move: (R_inc y) => /set1_P ->; rewrite B_eq.
Qed.

Lemma setIt_1 (a:Set)(x:a) (f: singleton (Ro x) -> Set):
  intersectiont  f = f (Bo (set1_1 (Ro x))).
Proof. 
apply: extensionality; first by apply:setIt_s1.
move => t ti; apply: setIt_i;[by fprops | move=> j]. 
have -> //: (j = (Bo (set1_1 (Ro x)))).
by apply: R_inj; move: (R_inc j) => /set1_P ->; rewrite B_eq.
Qed.



Lemma setUt_S (I:Set) (f g:I->Set):
  (forall i, sub (f i) (g i)) -> sub (uniont f) (uniont g).
Proof. 
by move=> su t /setUt_P [z tf]; apply/setUt_P; exists z; apply: su.
Qed.

Lemma setIt_S (I:Set)  (f g:I->Set):
  (forall i, sub (f i) (g i)) -> sub (intersectiont f) (intersectiont g).
Proof. 
move=> su.
case: (emptyset_dichot I) => i2; first by rewrite !setIt_0.
move=> t /(setIt_P _ i2) hyp; apply/setIt_P => //j; apply: su;apply: hyp.
Qed.



Theorem setCUt2 (I:Set) (f:I-> Set) x: nonempty I ->
  x -s (uniont f) = intersectiont (fun i=> x -s (f i)).
Proof. 
move=>neI; set_extens z.
  move /setC_P =>[zx zu];apply:(setIt_i neI) => j; apply setC_i => //.
  by dneg t; apply/ setUt_P; exists j.
move: neI=> [_ [i _]] xi; move: (setIt_hi i xi) => /setC_P [zx zu].
apply: setC_i => //;move /setUt_P => [j zj].
by move: (setIt_hi j xi) => /setC_P [_].
Qed.


Theorem setCIt2 (I:Set) (f:I-> Set) x: nonempty I ->
  x -s (intersectiont f) = uniont (fun i=> x -s (f i)).
Proof.
move=> neI.
set_extens t.
  move/setC_P => [tx ti]; apply/setUt_P; ex_middle bad.
  case: ti; apply /(setIt_P _ neI) => j;ex_middle bad2.
  case: bad; exists j; apply: setC_i => //.
move/setUt_P => [z /setC_P [tx tf]];apply: setC_i => // h. 
exact:(tf (setIt_hi z h)).
Qed.



End CoqFunctions.
