(** * Theory of Sets: EII-4 Union and intersection of a family of sets
  Copyright INRIA (2009-2013) (Apics) Marelle Team (Jose Grimm).
*)

Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Warnings "notation-overridden".
Require Export sset2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* $Id: sset3.v,v 1.8 2018/09/04 07:58:00 grimm Exp $ *)

Module Bunion.

(** ** EII-4-1 Definition of the union and intersection of a family of sets*)

(** Three definitions of union: a map of type [I-> Set],
a map of type [Set -> Set] and a functional graph. The definition is similar 
to that of a union of a set. 
There are also three definitions of intersection  *)

Definition intersectiont  (I:Set) (f : I->Set):= 
  Zo (uniont f) (fun y => forall z : I, inc y (f z)).

Definition unionf (x:Set)(f: fterm) := uniont (fun a:x => f (Ro a)). 
Definition unionb g := unionf (domain g)(Vg g). 
Definition intersectionf (x:Set)(f: fterm) := 
  intersectiont (fun a:x => f (Ro a)).
Definition intersectionb g := intersectionf (domain g) (Vg g).

(** Basic properties of union  *)

Lemma setUf_P x I f:
  inc x (unionf I f) <->  exists2 y, inc y I & inc x (f y).
Proof.  
split;first by move/setUt_P=> [z zp]; exists (Ro z) =>//; apply: R_inc. 
by move=>[y yi xf]; apply/setUt_P; exists (Bo yi); rewrite B_eq. 
Qed.

Lemma setUb_P x f:
  inc x (unionb f) <->  exists2 y, inc y (domain f) & inc x (Vg f y).
Proof. exact: setUf_P. Qed. 

Lemma setUb_P1 x a f:
   inc x (unionb (Lg a f)) <-> exists2 y, inc y a & inc x (f y).
Proof.
split.
  move /setUb_P; aw => - [y ya]; rewrite (LgV ya) => yf; ex_tac.
by move => [y ya xf]; apply /setUb_P; aw; ex_tac; bw. 
Qed.

Lemma setUf_i x y I f:
  inc y I -> inc x (f y) -> inc x (unionf I f).
Proof. by move=> yi xf;apply/setUf_P; exists y. Qed. 

Lemma setUb_i x y f:
  inc y (domain f) -> inc x (Vg f y) -> inc x (unionb f).
Proof. by move=> yd xv; apply/setUb_P; ex_tac. Qed.

Lemma setUf_hi x I f:
  inc x (unionf I f) ->  exists2 y, inc y I & inc x (f y).
Proof. by move/setUf_P. Qed.

Lemma setUb_hi x f:
  inc x (unionb f) ->  exists2 y, inc y (domain f) & inc x (Vg f y).
Proof. by move/setUb_P. Qed.


Ltac union_tac:= 
  match goal with
    | Ha : inc ?i (domain ?g), Hb :  inc ?x (Vg ?g ?i) |- inc ?x (unionb ?g)
      => apply: (setUb_i Ha Hb)
    | Ha : inc ?x ?y, Hb :  inc ?y ?a |- inc ?x (union ?a)
      => apply: (setU_i Ha Hb)
    | Ha : inc ?y ?i, Hb :  inc ?x (?f ?y) |- inc ?x (unionf ?i ?f)
      => apply: (setUf_i _ Ha Hb)
    | Ha : inc ?y ?i |- inc ?x (unionf ?i ?f)
      => apply: (setUf_i Ha); fprops
    | Hb : inc ?x (?f ?y) |- inc ?x (unionf ?i ?f)
      => apply: (setUf_i _ Hb); fprops
    | Ha : inc ?i (domain ?g) |- inc ?x (unionb ?g)
      => apply: (setUb_i Ha); fprops
    | Hb : inc ?x (Vg ?g ?i) |- inc ?x (unionb ?g)
      => apply: (setUb_i _ Hb); fprops
    | Hb : inc ?z ?X |- inc ?x (union ?X)
      => apply: (setU_i _ Hb); fprops
    | Ha : inc ?x ?z  |- inc ?x (union ?X)
      => apply: (setU_i Ha); fprops
  end.


(** If the index set is empty so are the union and intersection *)

Lemma setUf_0 f: unionf emptyset f = emptyset.
Proof. by apply/set0_P => x /setUf_P [y /in_set0]. Qed.

Lemma setUb_0: unionb emptyset = emptyset.
Proof. by rewrite / unionb; aw; apply: setUf_0.  Qed.

Lemma setIf_0 f: intersectionf emptyset f = emptyset.
Proof. apply/set0_P => t /Zo_S /setUt_P; case; case. Qed.

Lemma setIb_0: intersectionb emptyset = emptyset.
Proof. rewrite /intersectionb domain_set0; apply/setIf_0. Qed.

(** Basic properties of the intersection in the non-trivial case *)

Lemma setIt_P (I:Set) (f:I-> Set): nonempty I -> forall x,
  (inc x (intersectiont f) <-> (forall j, inc x (f j))).
Proof. 
move=> [i [ix _]];split; first by move /Zo_hi.
move => h1; apply: Zo_i => //; apply /setUt_P; exists ix; apply: (h1 ix).
Qed.

Lemma setIf_P I f:  nonempty I -> forall x,
  (inc x (intersectionf I f) <-> (forall j, inc j I -> inc x (f j))).
Proof.
move => h x; split; first by move/(setIt_P _ h) => aux j [ji <-]; apply: aux.
move => aux; apply/(setIt_P _ h) => j; apply: aux; apply: R_inc.
Qed.

Lemma setIb_P g: nonempty g -> forall x,
  (inc x (intersectionb g) <-> (forall i, inc i (domain g) -> inc x (Vg g i))).
Proof. move/domain_set0P => h x; exact: (setIf_P _ h). Qed.


Lemma setI_P y: nonempty y -> forall x,
  (inc x (intersection y) <-> (forall i, inc i y -> inc x i)).
Proof.
by move=> ney; split; [ move=> xi iy; apply: setI_hi | apply: setI_i].
Qed.


Lemma setIf_i I f x: nonempty I ->
  (forall j, inc j I -> inc x (f j)) -> inc x (intersectionf I f).
Proof. by move=> pa pb; apply/setIf_P. Qed.

Lemma setIf_hi I f x j:
  inc x (intersectionf I f) -> inc j I -> inc x (f j).
Proof. move => pa pb; move /(setIf_P): pa; apply => //; ex_tac. Qed.

Lemma setIb_i g x:  nonempty g ->
  (forall i, inc i (domain g) -> inc x (Vg g i)) -> inc x (intersectionb g).
Proof. by move=> neg h; apply/setIb_P. Qed.

Lemma setIb_hi g x i:
  inc x (intersectionb g) -> inc i (domain g) -> inc x (Vg g i).
Proof. 
by move => /setIb_P pa pb; apply: pa => //; apply /domain_set0P; ex_tac.
Qed.


Lemma setUf_exten I f f':
  {inc I, f =1 f'} -> unionf I f = unionf I f'.
Proof.
move=> hyp; set_extens t;move/setUf_P=> [z zi tf]; apply/setUf_P; ex_tac.
  by rewrite -hyp. 
by rewrite hyp.  
Qed.

Lemma setU_bf X f:  unionf X f = unionb (Lg X f).  
Proof. by rewrite/unionb; aw;apply:setUf_exten => t tX; bw. Qed.

Lemma setIf_exten I f f':  {inc I, f =1 f'} ->
  intersectionf I f  = intersectionf I f'.
Proof. 
move=> sv; case: (emptyset_dichot I) => ine.
  by rewrite ine !setIf_0.
set_extens t => /(setIf_P _ ine) h;apply/(setIf_P _ ine) => j jI.
- by rewrite - (sv _ jI); apply: h.
- by rewrite (sv _ jI); apply: h.
Qed.

(** Proposition 1 : [union (compose g f) = union g] *)

Lemma setUb_rewrite f g:
  fgraph f -> range f = domain g -> 
  unionb g = unionb (g \cf f).
Proof. 
rewrite /composef=>  fgf rfsg.
set_extens t; move/setUb_P => [a pa pb]; apply/setUb_P.
  move: pa; rewrite- rfsg; move /(range_gP fgf) => [x xd etc].
  aw; ex_tac; rewrite LgV //; ue.
move: pa;aw => pa.
move: pb; rewrite LgV // - rfsg => ta; exists (Vg f a); fprops. 
Qed.

Lemma setUb_rewrite1 f g:
  function f -> fgraph g -> Imf f = domain g -> 
  unionb g = unionb (g \cf (graph f)).
Proof.
move => ff; rewrite (ImfE ff) => fgg; apply: setUb_rewrite.
by case:ff.
Qed.

Lemma setIb_rewrite  f g:
  fgraph f -> range f = domain g ->
  intersectionb g = intersectionb (g \cf f).
Proof.
move=> fgf rfdg. 
case: (emptyset_dichot g) => gp.
  symmetry;congr intersectionb; rewrite gp; apply /set0_P=> t /funI_P [z zd _].
  have :(inc (Vg f z) (range f)) by fprops.
  rewrite rfdg gp domain_set0; apply: in_set0.
have nec: (nonempty (g \cf f)). 
  move: gp => [x xg].
  have : (inc (P x) (range f)) by  rewrite rfdg; fprops.
  move/(range_gP fgf) => [y ydf etc].
  exists (J y (Vg g (Vg f y))); apply/funI_P; ex_tac.
set_extens t.
  move/(setIb_P gp) => h; apply/(setIb_P nec); rewrite /composef; aw => j jdf.
  rewrite LgV //; apply: h; rewrite - rfdg; apply range_gP => //; ex_tac.
move/(setIb_P nec) => h; apply/(setIb_P gp) => i; rewrite -rfdg.
move/(range_gP fgf) => [x xdf ->]; move: (h x);rewrite Lgd  LgV //.
by apply.
Qed.


(** Union and intersection of a function with singleton range *)


Lemma setUf_1 f x: unionf (singleton x) f = f x.
Proof. 
by set_extens t => tp; [ move: (setUf_hi tp)=> [y  /set1_P ->] | union_tac ].
Qed.

Lemma setIf_1 f x: intersectionf (singleton x) f = f x.
Proof. 
set_extens t => tx; first  exact :(setIf_hi tx (set1_1 x)).
apply: setIf_i; [ fprops | by move=> j; move/set1_P => ->].
Qed.

Lemma setUb_constant f x: constantgp f -> inc x (domain f) ->
  unionb f = Vg f x.
Proof.
move => p1 p2; set_extens t; last by move => p3; union_tac.
by move /setUb_P => [y y1 y2]; rewrite (proj2 p1 _ _ p2 y1).
Qed.

Lemma setIb_constant f x: constantgp f -> inc x (domain f) ->
  intersectionb f = Vg f x.
Proof.
move => p1 p2. 
have nef: nonempty f by apply /domain_set0P; ex_tac.
set_extens t; first by move /(setIb_P nef); apply.
by move => h; apply  /(setIb_P nef) => i idf;rewrite (proj2 p1 _ _ idf p2).
Qed.

(** Link between union and unionb *)

Lemma setU_prop x: union x = unionf x id.
Proof. by []. Qed.

Lemma setI_prop x: intersection x = intersectionf x id.
Proof. 
case: (emptyset_dichot x) => xe; first by rewrite xe setI_0 setIf_0.
set_extens t; first by move/(setI_P xe) =>h; apply:setIf_i.
by move/(setIf_P _ xe) =>h;apply:setI_i.
Qed.

Lemma setUb_alt f: fgraph f -> unionb f = union (range f).
Proof. 
move=> fgf.
set_extens t; first by move/setUb_P=> [y ty yx]; union_tac.
move/setU_P => [z te]; move/(range_gP fgf) => [x xd eq]; union_tac; ue.
Qed.

Lemma setUb_identity x: unionb (identity_g x) = union x.
Proof. 
rewrite /unionb identity_d setU_prop. 
by apply: setUf_exten => i ix /=; rewrite identity_ev. 
Qed.

Lemma setIb_alt f: fgraph f -> intersectionb f = intersection (range f).
Proof. 
move => fgf; case: (emptyset_dichot f) => fe.
  by rewrite fe range_set0 setI_0 setIb_0.
set_extens t.
  move => ti; apply:setI_i.
    move: fe => [w tf]; exists (Q w); apply/funI_P; ex_tac.
  move=> y /(range_gP fgf) [x xdf ->]; exact: (setIb_hi ti xdf).
move => ti; apply:setIb_i => // i idf; apply: (setI_hi ti).
apply /(range_gP fgf); ex_tac.
Qed.

Lemma setIb_identity x: intersectionb (identity_g x) = intersection x.
Proof. 
rewrite /intersectionb identity_d setI_prop. 
by apply: setIf_exten; move=> i ix /=; rewrite identity_ev. 
Qed.

(** ** EII-4-2 Properties of union and intersection *)

(** Monotony properties *)

Lemma setUf_S2 f: {compat (unionf ^~ f) : x y / sub x y }.
Proof. move => x y /= sab t /setUf_P [z yA tfy]; union_tac.  Qed.

Lemma setIf_S f:
  {compat (intersectionf ^~ f) : x y / sub x y /\ nonempty x >-> sub y x}.
Proof. 
move=> A B [sAB neA].
have neB: (nonempty B) by move:neA=> [x]; exists x; apply: sAB.
by move=> x /(setIf_P _ neB) p; apply:(setIf_i neA) =>j jA; apply:p; apply: sAB.
Qed.

(** Associativity of union and intersection  *)

Theorem setUf_A L f g:
  unionf (unionf L g) f = unionf L (fun l => unionf (g l) f).
Proof. 
set_extens t; move /setUf_P=> [y yu tfy]; [ move: yu | move: tfy];
  move/setUf_P => [z zsg ygz]; apply/setUf_P; exists z =>//; union_tac.
Qed.

Theorem setIf_A L f g:
  (alls L (fun i => (nonempty (g i)))) ->
  intersectionf (unionf L g) f
   = intersectionf L (fun l => intersectionf (g l) f).
Proof. 
move=> neall.
case: (emptyset_dichot L) => sgp;first by rewrite sgp setUf_0 // 2! setIf_0. 
have neu: (nonempty (unionf L g)). 
  by move: sgp=> [x xsg]; move: (neall _ xsg)=> [y iy]; exists y; union_tac.
set_extens t.
  move/(setIf_P _ neu) => h; apply: (setIf_i sgp) => j jsg. 
  apply: (setIf_i (neall _ jsg)) => k kj; apply: h; union_tac.
move/(setIf_P _ sgp) => h; apply: (setIf_i neu) => j /setUf_P [y ysg jgy].
exact (setIf_hi (h _ ysg) jgy).
Qed.

(** ** EII-4-3 Images of a union and an intersection *)

Theorem dirim_setUf I f g:
  direct_image g (unionf I f) = unionf I (fun i => direct_image g (f i)).
Proof. 
set_extens t. 
  move /dirim_P=> [x /setUf_P [y yI xfy] Ju]; apply /setUf_P. 
  exists y => //; apply/dirim_P; ex_tac.
move /setUf_P => [z zI /dirim_P [x xf Jg]].
apply /dirim_P;ex_tac; union_tac.
Qed.

Theorem dirim_setIf I f g:
  sub (direct_image g (intersectionf I f))
  (intersectionf I (fun i => direct_image g (f i))).
Proof. 
move => t /dirim_P [x].
case: (emptyset_dichot I) => neI; first by rewrite neI setIf_0 => /in_set0.
move => ta tb; apply: (setIf_i neI) => j jI; apply/dirim_P; ex_tac.
apply: setIf_hi ta jI.
Qed.

Theorem iim_fun_setIf I f g:
  function g ->  
  (Vfi g (intersectionf I f)) = (intersectionf I (fun i => Vfi g (f i))).
Proof. 
move=> fg.
apply: extensionality; first by rewrite iim_fun_pr; apply:dirim_setIf.
case: (emptyset_dichot I) => ie; first by rewrite ie setIf_0 ; fprops.
move => t /(setIf_P _ ie) aj.
move: (ie)=> [x xI]; move: (aj _ xI) => /iim_fun_P[u ufz Jg].
apply/iim_fun_P; ex_tac; apply: (setIf_i ie) => v /aj.
move => /iim_graph_P [u' ufx Jg'].
by rewrite (Vf_pr fg Jg); rewrite - (Vf_pr fg Jg').  
Qed.

Lemma inj_image_setIf I f g:
  injection g ->
  (Vfs g (intersectionf I f)) = (intersectionf I (fun i => Vfs g (f i))).
Proof.
move=> ig; move: (proj1 ig) => fg.
have [_ _ _ _ aux]:= (canonical_decomposition1 fg).
have sf := (iim_fun_r fg).
rewrite sf iim_fun_setIf; last by apply: (bijective_inv_f (aux ig)).
by apply: setIf_exten.
Qed. 

(** ** EII-4-4 complement of unions and intersections *)

Lemma setCUf2 I f x: nonempty I ->  
  x -s (unionf I f) = intersectionf I (fun i=> x -s (f i)).
Proof.
move => neI; set_extens z.
  move /setC_P =>[zx zu];apply:(setIf_i neI) => j jI; apply setC_i => //.
  dneg t; union_tac.
move: neI=> [i iI] xi; move: (setIf_hi xi iI) => /setC_P [zx zu].
apply: setC_i => // /setUf_P  [j jI zj].
by case/setC_P: (setIf_hi xi jI).
Qed.

Lemma setCIf2 I f x: nonempty I ->  
  x -s (intersectionf I f) = unionf I (fun i=> x -s (f i)).
Proof. 
move=> neI;set_extens t.
  move/setC_P => [tx ti]; apply/setUf_P; ex_middle bad.
  case: ti;apply /(setIf_P f neI) => j jI;ex_middle bad2. 
  by case: bad; exists j => //; apply: setC_i.
move/setUf_P => [z zI /setC_P [tx tf]];apply: setC_i => // h. 
exact:(tf (setIf_hi h zI)).
Qed.


(** ** EII-4-5 union and intersection of two sets *)

Lemma setUf2f x y f:
  unionf (doubleton x y) f = (f x) \cup (f y).
Proof. 
set_extens t;last by case /setU2_P=> tf; union_tac.
move/setUf_P => [z /set2_P []] -> h; fprops.
Qed. 

Lemma setIf2f x y f:
  intersectionf (doubleton x y) f = (f x) \cap (f y).
Proof. 
have ned:= (set2_ne x y).
set_extens z.  
  move /(setIf_P _ ned) => h; apply setI2_i; apply: h; fprops.
by move/setI2_P => [zx zy]; apply: (setIf_i ned) => j; case/set2_P => ->.
Qed.

Lemma setUf2 x y: unionf (doubleton x y) id = x \cup y.
Proof. by rewrite setUf2f.  Qed. 

Lemma setIf2 x y: intersectionf (doubleton x y) id =  x \cap y.
Proof. by rewrite setIf2f. Qed.

Lemma dirim_setU2 g: {morph (direct_image g): x y / x \cup y}.
Proof. by move => x y /=; rewrite - setUf2f - setUf2 dirim_setUf. Qed.

Lemma dirim_setI2 g x y:
  sub (direct_image g (x \cap y))
  ((direct_image g x) \cap (direct_image g y)).
Proof. rewrite - setIf2f - setIf2; apply: dirim_setIf. Qed.

Lemma iim_fun_setI2 g: function g -> 
  {morph (Vfi g): x y / x \cap y}.
Proof.
by move => fg x y /=;  rewrite - setIf2f - setIf2; apply iim_fun_setIf.
Qed.

Lemma iim_fun_C1 f: function f ->
 {when  eq^~ (target f) & sub^~ (target f),
   {morph Vfi f : a b / a -s b}}.
Proof.
move => ff a b -> btf.
set_extens t.
  move/iim_fun_P=> [u /setC_P [utf ux] Jg];apply: setC_i.
    apply/iim_fun_P;ex_tac.
  by move/iim_fun_P=>[v vx Jvg]; case: ux;rewrite (Vf_pr ff Jg) -(Vf_pr ff Jvg).
move/setC_P => [/iim_fun_P [u ut Jg] ne]; apply/iim_fun_P; ex_tac.
apply/setC_i => //;dneg h; apply/iim_fun_P; ex_tac.
Qed.


Lemma inj_image_C f: injection f -> 
 {when eq^~ (source f) & sub^~ (source f),
   {morph Vfs f : a b / a -s b}}.
Proof. 
move=> ig a b ->; move: (proj1 ig) => fg.
have [_ fv _ _ aux] := (canonical_decomposition1 fg).
rewrite 3! (iim_fun_r fg).
have ->: source f = target (inverse_fun (restriction_to_image f)). 
  by rewrite {1} fv; aw.
by apply: iim_fun_C1 => //; apply: (bijective_inv_f (aux ig)).
Qed.


(** ** EII-4-6 Coverings  *)

(** We define a covering for a map, a function, and a set of sets *)

Definition covering f x :=  fgraph f /\ sub x (unionb f).
Definition covering_s f x := sub x (union f).

Lemma covering_P f x: fgraph f -> 
   (covering f x <-> covering_s (range f) x).
Proof.
move => fgf; rewrite /covering/covering_s setUb_alt //. 
by split; [case | split ].
Qed.

(** Two definitions, second one will be used in set5 *)

Definition coarser_cg f g :=
  [/\ fgraph f, fgraph g &
  forall j, inc j (domain g) 
    -> exists2 i, inc i (domain f) &  sub (Vg g j) (Vg f i)].

Definition coarser_cs y y':=
  forall a, inc a y' -> exists2 b, inc b y & sub a b.

Lemma coarser_cP f g: fgraph f -> fgraph g ->
  (coarser_cg f g <-> coarser_cs (range f) (range g)).
Proof.
move => fgf fgg;split.
  move=> [_ _ cc j]; move/(range_gP fgg) => [i id ->].
  move: (cc _ id) => [k kdf h];exists (Vg f k) => //.
  apply/(range_gP fgf); ex_tac.
move => cc; split => // j jdg.
move: (cc _ (inc_V_range fgg jdg)) => [i /(range_gP fgf) [k kdf ->] h].
ex_tac.
Qed.

Lemma sub_covering f I x (g := restr f I):
  (sub I (domain f)) -> covering f x -> covering g x -> 
  coarser_cg f g.
Proof. 
move => sd [fgf cf] [fgg cg]; split => // j; rewrite restr_d => jJ.
move: (sd _ jJ) => jdf; ex_tac; rewrite /g restr_ev //.
Qed.

(** We consider the family of intersections of two families *)

Definition intersection_covering f g :=
  Lg ((domain f) \times (domain g))
    (fun z => (Vg f (P z)) \cap (Vg g (Q z))).

Definition intersection_covering2 x y:=
  range (intersection_covering (identity_g x) (identity_g y)).

Lemma setI_covering2_P x y z:
  inc z (intersection_covering2 x y) <->
  exists a b, [/\ inc a x, inc b y &  a \cap  b = z].
Proof.
rewrite /intersection_covering2 /intersection_covering 2! identity_d.
split.
  move/Lg_range_P => [b /setX_P [pb Pb Qb] ->].
  by rewrite identity_ev // identity_ev //; exists (P b), (Q b). 
move => [a [b [ax iby <-]]]; apply/Lg_range_P.
exists (J a b); [ fprops | aw;rewrite identity_ev // identity_ev //].
Qed.

Lemma setI_covering E: {compat intersection_covering : x & / covering x E}.
Proof.
move => f g  [fgf c1] [fgg c2].
rewrite /intersection_covering; split; first by fprops.
move => u ux; move /setUb_P: (c1 _ ux) => [a af uf].
move/setUb_P:(c2 _ ux)=> [b bg ug].
have jj: inc (J a b) (domain f \times domain g) by fprops.
apply/setUb_P;aw;exists (J a b) => //; rewrite LgV //; aww.
Qed.

Lemma setI_coarser_cl f g x:
  covering f x -> covering g  x ->
  coarser_cg f (intersection_covering f g).
Proof. 
move=> [fgf c1] [fgg c2].
rewrite /intersection_covering; hnf; split; aww.
move => j ji; move /setX_P:(ji)=> [pj Pj Qj]; ex_tac => t.
rewrite LgV //; apply: setI2_1.
Qed.

Lemma setI_coarser_cr f g x:
  covering f x -> covering g  x ->
  coarser_cg g (intersection_covering f g).
Proof. 
move=> [fgf c1] [fgg c2]. 
rewrite /intersection_covering; hnf;split; aww.
move => j ji;move /setX_P: (ji)=> [pj Pj Qj]; ex_tac => t.
rewrite LgV //; apply: setI2_2.
Qed.

Lemma setI_coarser_clr h x:
  covering h x -> {when covering ^~ x &,
      {compat intersection_covering : f & /  coarser_cg f h}}.
Proof.
move => c3 f g c1 c2 [fgf fhg cc1] [fgg _ cc2].
rewrite /intersection_covering /coarser_cg; split;aww.
move => u udh. 
move: (cc2 _ udh)(cc1 _ udh) => [i isg s1] [j jsf s2].
have pd: inc (J j i) (domain f \times domain g) by fprops.
exists (J j i) => //; rewrite LgV //; aw.
by move=> v vh; apply/setI2_i; [apply: s2 |apply: s1].
Qed.


(** Next four lemmas are a rewrite of above; they say that 
   [intersection_covering2] is the supremum of both args *)

Lemma setI_covering2 E:
  {compat intersection_covering2 : x & / covering_s x E}.
Proof.
move=> u v c1 c2 z zu.
move /setU_P: (c1 _ zu) =>[y zy yu].
move /setU_P: (c2 _ zu) =>[y' xzy' yv].
apply/setU_P;exists (y \cap y'); first  by fprops.
by apply/ setI_covering2_P; exists y, y'.
Qed. 

Lemma setI_coarser2_cl f g x:
  covering_s f x -> covering_s g x ->
  coarser_cs f (intersection_covering2 f g).
Proof. 
move=> c1 c2 z; move/setI_covering2_P=> [a [b [af bg <-]]]. 
ex_tac; apply: subsetI2l.
Qed.

Lemma  setI_coarser2_cr f g x:
  covering_s f x -> covering_s g x ->
  coarser_cs g (intersection_covering2 f g).
Proof. 
move=> c1 c2 z; move/setI_covering2_P=> [a [b [af bg <-]]]. 
ex_tac; apply: subsetI2r.
Qed.

Lemma  setI_coarser2_clr h x:
  covering_s h x -> {when covering_s ^~ x &,
      {compat intersection_covering2 : f & / coarser_cs f h}}.
Proof. 
move=> c23 f g c1 c2 cc1 cc2 t th.
move: (cc1 _ th) (cc2 _ th)=> [b bf tb] [b' bg tb'].
exists (b \cap b').
  by apply/setI_covering2_P; exists b, b'.
by apply: setI2_12S.
Qed.

(** We consider the direct and inverse image of a covering, and the product of two coverings *)

Lemma image_of_covering f g:
  surjection g -> covering  f (source g) ->
  covering (Lg (domain f) (fun w => Vfs g (Vg f w))) (target g).
Proof. 
move=> [fg sg] [fgf cf]; split; first by fprops.
move => x xtg; move: (sg _ xtg)=> [y ys vg]. 
move:(setUf_hi (cf  _ ys)) => [z zsf yfz]. 
apply/setUb_P; aw; ex_tac; rewrite LgV // vg.
apply/dirim_P; ex_tac; Wtac.
Qed.

Lemma inv_image_of_covering f g:
  function g -> covering f (target g) ->
  covering (Lg(domain f) (fun w => Vfi g (Vg f w))) (source g).
Proof. 
move=> fg [fgf cf]; split; first by fprops. 
move => x xs; apply/setUb_P; aw.
have Wt: (inc (Vf g x) (target g)) by fprops.
move /setUb_P: (cf _ Wt) => [y ysf Wf]; ex_tac; rewrite LgV //.
apply/iim_fun_P; ex_tac; Wtac.
Qed.

Lemma product_of_covering f g x y:
  covering f x -> covering g y ->
  covering (Lg ((domain f) \times (domain g))
        (fun z =>  (Vg f (P z)) \times (Vg g (Q z))))
    (x \times y).
Proof. 
move=> [fgf c1] [fgg c2]; split; first by fprops.
move => z /setX_P [zp px qy].
move /setUb_P: (c1 _ px) => [a asf pa].
move /setUb_P: (c2 _ qy) => [b bsg ab].
have pc: inc (J a b) ((domain f) \times (domain g)) by fprops.
by apply/setUb_P;exists (J a b); aw;trivial;  rewrite LgV //; aw;apply:setX_i.
Qed.

(** If two functions agree on each element of a covering of X, they agree on X *)

Lemma agrees_on_covering  f x g g':
  covering f x -> function g -> function g' ->
  source g = x -> source g' = x -> 
  (forall i, inc i (domain f) ->  agrees_on (x \cap (Vg f i)) g g') ->
  agrees_on x g g'.
Proof.
move=> [fgf c] fg fg' sg sg' ag.
hnf; rewrite sg sg';split; fprops.
move=> a ax; move /setUb_P: (c _ ax) => [y ysf afy].
by apply: (proj33 (ag _ ysf)); apply: setI2_i.
Qed.


(** We consider the fonction whose source is the union of a family [f], 
the target is [t], the graph is the union of all [h i], which are functions 
defined  [V i f] with a compatibility condition  *)

Definition common_ext f h t:=
  triple (unionb f) t (unionb (Lg (domain f) (fun i => (graph (h i))))). 

Definition function_prop_sub f s t:= 
  [/\ function f, source f = s & sub (target f) t]. 

Lemma extension_covering f t h 
  (d:= domain f) (g := common_ext f h t) :
  (forall i, inc i d -> function_prop (h i) (Vg f i) t) ->
  (forall i j, inc i d -> inc j d -> 
    agrees_on ((Vg f i) \cap  (Vg f j)) (h i) (h j)) ->
  [/\ function_prop g (unionb f) t,
    graph g = (unionb (Lg d (fun i => (graph (h i))))),
    Imf g = unionb  (Lg d (fun i => (Imf (h i)))) &
    (forall i, inc i d -> agrees_on (Vg f i) g (h i))].
Proof.
move=> afp aag.
have sg: (source g = unionb f) by rewrite /g /common_ext; aw.
have tg: (target  g = t) by rewrite /g/common_ext; aw.
set u1:= unionb (Lg _ _).
have gg: graph g = u1 by rewrite /u1/g/common_ext; aw.
have gu: sgraph u1.
  move=> z /setUb_P; aw;move=> [y yd]; rewrite LgV // => zd.
  by move: (afp _ yd) => [ff _ _]; move: (function_sgraph ff); apply.
have fgf: fgraph u1.
  rewrite /u1;split=>//.
  move => x y /setUb_P [u usf xghu] /setUb_P [v vsf yghv] sp.
  move: usf vsf; aw => usf vsf; move:xghu yghv.
  rewrite !LgV // =>  xghu yghv.
  move:(afp _ usf) (afp _ vsf) => [fu shu _] [fv shv _].
  move: (Vf_pr2 fu xghu)(Vf_pr2 fv yghv) => qx qy. 
  apply: pair_exten=>//.
      by apply: (function_sgraph fu).  
    by apply: (function_sgraph fv).  
  rewrite qx qy sp; apply: (proj33 (aag _ _ usf vsf)).
  by rewrite - shu - shv; apply: setI2_i ;[ rewrite - sp|]; Wtac.
have fg: function g. 
  rewrite /g/common_ext; apply: function_pr=>//. 
    move=> z /funI_P [x /setUb_P];aw;move=> [y ysf].
    rewrite LgV // => Jg ->.
    by move: (afp _ ysf)=> [fhy _ <-]; Wtac.
  set_extens z.
    move /setUb_P=> [y ysf zfy]; apply/(domainP gu); exists (Vf (h y) z).
    move: (afp _ ysf) => [fhy shy  _].
    apply /setUb_P; aw; ex_tac; bw  => //;  apply: Vf_pr3 => //; ue. 
  move/(domainP gu) => [y]; move/setUb_P; aw;move=> [x xsf]; bw => // jg.
  move: (afp _ xsf) => [fhx shx _]; apply/setUb_P;ex_tac; rewrite - shx; Wtac.
split => //.
  rewrite (ImfE fg) /g/common_ext; aw; set_extens zs.
    move/(rangeP gu)=> [x] /setUb_P; aw. 
    move =>[y ysf]; rewrite LgV // =>  zfy.  
    apply/setUb_P;move: (afp _ ysf) => [fhy shy _]; aw; ex_tac.
    rewrite LgV // (ImfE fhy); ex_tac.
  move/setUb_P; aw; move=> [y ysf]; bw => //.
  move: (afp _ ysf) => [fhy shy _];rewrite (ImfE fhy).
  move /(rangeP (function_sgraph fhy)) => [x Jg]. 
  apply/(rangeP gu); exists x; apply/setUb_P;  aw; ex_tac; rewrite LgV //.
move=> y ysf; move: (afp _ ysf) => [fhy shy _].
split; first by rewrite sg; move=> x xfy; union_tac.
  by rewrite shy; fprops.
move=> a afy /=; symmetry;apply: Vf_pr => //.
rewrite gg; apply /setUb_P; aw; ex_tac; rewrite LgV //; Wtac; ue.
Qed.

Lemma extension_covering_thm f t h (d:= domain f):
  (forall i, inc i d -> function_prop (h i) (Vg f i) t) ->
  (forall i j, inc i d -> inc j d -> 
    agrees_on ( (Vg f i) \cap (Vg f j)) (h i) (h j)) ->
  fgraph f -> 
  exists! g, (function_prop g (unionb f) t /\
    (forall i, inc i d -> agrees_on (Vg f i) g (h i))).
Proof. 
move=> afp aag fgf; apply /unique_existence;split.
  move: (extension_covering afp aag)=> [p1 p2 p3 p4].
  by exists (common_ext f h t).
rewrite /function_prop=> x y [[fx sx tx] agx]  [[fy sy ty] agy]. 
apply: function_exten=>//; try  ue.
have c: (covering f (unionb f)) by split => //.
suff agi: (forall i, inc i d -> agrees_on ((unionb f) \cap (Vg f i)) x y).
  move:(proj33 (agrees_on_covering c fx fy sx sy agi)); rewrite sx;apply.
move=> i isf; hnf. 
split;first by rewrite sx;apply: subsetI2l.
  by rewrite sy;apply: subsetI2l.
move => a /setI2_P; move: (proj33 (agx _ isf)) (proj33 (agy _ isf)).
rewrite /agrees_on; move=> p1 p2 [_ afi].
by rewrite (p1 _ afi) (p2 _ afi).
Qed.


(** ** EII-4-7 Partitions  *)

(** A partition is a kind of covering formed of mutually disjoint sets.
  We may assume the sets non-empty *)

Definition nonempty_fam f := allf f nonempty.
Definition disjoint_set X :=
  (forall a b, inc a X -> inc b X -> disjointVeq a b).

Definition mutually_disjoint f :=
  (forall i j, inc i (domain f) -> inc j (domain f) -> 
    i = j \/ (disjoint (Vg f i) (Vg f j))).

Definition partition_w y x:=
  (union y = x) /\ disjoint_set y.


Definition partition_s y x:= partition_w y x /\ (alls y nonempty).

Definition partition_w_fam f x:=
  [/\ fgraph f, mutually_disjoint f & unionb f = x].

Definition partition_s_fam f x:=
  partition_w_fam f x /\ nonempty_fam f.

Lemma mutually_disjoint_prop f:
  (forall i j y, inc i (domain f) -> inc j (domain f)  ->
    inc y (Vg f i) -> inc y (Vg f j) -> i = j) ->
  mutually_disjoint f.
Proof. 
move=> hyp i j idf jdf; mdi_tac nij => u ui uj; case: nij; exact: (hyp _ _ u).
Qed.

Lemma mutually_disjoint_prop1 f: function f ->
  (forall i j y, inc i (source f) -> inc j (source f)  ->
    inc y (Vf f i) -> inc y (Vf f j) -> i = j) ->
  mutually_disjoint (graph f).
Proof.
by move=> ff hyp; apply: mutually_disjoint_prop; rewrite domain_fg.
Qed.

Lemma mutually_disjoint_prop2 x f:
  (forall i j y, inc i x -> inc j x  ->
    inc y (f i) -> inc y (f j) -> i = j) ->
  mutually_disjoint (Lg x f).
Proof. 
move=> hyp; apply: mutually_disjoint_prop; aw => i j y ix jy.
by rewrite !LgV //; apply: hyp. 
Qed.

Lemma partition_same y x:
  partition_w y x -> partition_w_fam (identity_g y) x.
Proof.
move=> [un di]; hnf; rewrite setUb_identity.
split => //; first by apply: identity_fgraph.
hnf; rewrite identity_d => i j iy jy.
by rewrite ! identity_ev //; apply: di. 
Qed.

Lemma partition_same2 y x:
  partition_w_fam y x -> partition_w (range y) x.
Proof. 
move=> [fg md uyx]; split; first by rewrite - setUb_alt. 
move=> a b /(range_gP fg) [u ud ->] /(range_gP fg) [v vd ->].
by case: (md _ _ ud vd) ;[ move=>->|]; [left | right].
Qed.

Lemma partitions_is_covering y x:
  partition_w y x -> covering_s y x.
Proof. by  move=> [u d] a ax; ue. Qed.

Lemma partition_fam_is_covering y x:
  partition_w_fam y x -> covering y x.
Proof. move=> [fg md uyx];split=>//; rewrite uyx; fprops. Qed.

(** If [f] is a partition of [x] each element of [x] is uniquely [V i f ] *)

Definition cover_at f y := select (fun i => inc y (Vg f i)) (domain f).

Lemma cover_at_in f x y (i := cover_at f y):
  partition_w_fam f x -> inc y x ->
  (inc y (Vg f i) /\ inc i (domain f)).
Proof.
move=>  [fg md ufx] yx; apply: select_pr.
  by move: yx; rewrite - ufx; move/setUb_P.
move=> k j id yif jd yjf.
have yi: (inc y ((Vg f k) \cap (Vg f j))) by fprops.
case: (md k j id jd) =>// di;empty_tac1 y.
Qed.

Lemma cover_at_pr f x y i:
   partition_w_fam f x -> inc i (domain f) -> inc y (Vg f i) ->
   cover_at f y = i.
Proof.
move => h idf yv.
have [fgf md uf] := h.
have zx: inc y x by rewrite -uf; union_tac.
have [yfc cd]:= (cover_at_in h zx).
case: (md _ _ cd idf) => // di; empty_tac1 y.
Qed.

Lemma same_cover_at f x y z (i := cover_at f y):
  partition_w_fam f x -> inc y x -> inc z (Vg f i) ->  cover_at f z = i.
Proof.
move => pf yx zi.
exact: (cover_at_pr pf (proj2 (cover_at_in pf yx)) zi).
Qed.

(** [coarser] is an ordering of partitions *)

Lemma coarserT:  transitive_r coarser_cs.
Proof.
move=> z x y c1 c2 u uy.
move: (c2 _ uy)=> [v zy uz]; move: (c1 _ zy)=> [t ty zt].
by ex_tac; apply: (sub_trans uz zt).
Qed.

Lemma coarserR: reflexive_r coarser_cs.
Proof. by move=> s x xy; ex_tac. Qed.

Lemma coarserA x: 
  {when partition_s ^~ x &, antisymmetric_r coarser_cs}.
Proof.  
suff: (forall y y',  partition_s y x ->  partition_s y' x ->
       coarser_cs y y' -> coarser_cs y'  y -> sub y y').
  move=> hyp u v p1 p2 c1 c2.
  apply: extensionality; first exact: (hyp _ _  p1 p2 c1 c2).
  by apply: (hyp _ _ p2 p1 c2 c1).
move=> y y' [p1 ne] _ c1 c2 t ty.
move: (c2 _ ty)(ne _ ty) => [b by' tb] [z zt].
move:(c1 _ by') => [a ay ba].
case: ((proj2 p1) _ _ ty ay) => eq; last by empty_tac1 z.
have -> //: t = b by apply: extensionality=>//; rewrite eq.
Qed.

(** We consider the function that associates [x] to [a] and [y] 
to anything else. This is generally defined on [doubleton a b] *)

Definition variant a x y := (fun z:Set => Yo (z = a) x y).
Definition variantL a b x y := Lg (doubleton a b) (variant a x y).

Lemma variant_true0 a x y :
  variant a x y a = x.
Proof. by rewrite /variant Y_true. Qed.

Lemma variant_true a x y z:
  z = a -> variant a x y z = x.
Proof. by move ->; apply:variant_true0. Qed.

Lemma variant_false a x y z:
  z <> a -> variant a x y z = y.
Proof. by move=> za; rewrite /variant Y_false. Qed.

(** We consider here the functions that maps elements of [a] to [x], anything else to [y] *)

Definition varianti x a b := fun z => Yo (inc z x) a b.

Lemma varianti_in z x a b: inc z x -> (varianti x a b z) = a.
Proof. by move=> zx; rewrite /varianti; Ytac0. Qed.

Lemma varianti_out z x a b: ~ inc z x -> (varianti x a b z) = b.
Proof. by move=> zx; rewrite /varianti; Ytac0. Qed.

Lemma variant_V_a  a b x y: Vg (variantL a b x y) a = x.
Proof. by rewrite LgV; [  apply: variant_true | fprops].  Qed.

Lemma variant_V_b a b x y:  b <> a -> Vg (variantL a b x y) b = y.
Proof. by rewrite LgV; [  apply: variant_false | fprops]. Qed.

Lemma variant_fgraph a b x y: fgraph (variantL a b x y).
Proof. rewrite/variantL;fprops. Qed.

Lemma variant_d a b x y:  domain (variantL a b x y) = doubleton a b.
Proof. by rewrite/variantL; aw. Qed.

Definition variantLc f g:=  variantL C0 C1 f g.

Lemma variantLc_fgraph x y:  fgraph (variantLc x y).
Proof. rewrite/variantLc/variantL; fprops. Qed.

Hint Resolve variant_fgraph variantLc_fgraph: fprops.

Lemma variantLc_d f g: domain (variantLc f g) = C2.
Proof. by rewrite/variantLc/variantL; aw. Qed.

Hint Rewrite variantLc_d: aw.

Lemma variantLc_domain_ne f g:  nonempty (domain (variantLc f g)).
Proof. aw; exists C0; fprops. Qed.

Lemma variantLc_prop x y:
  variantLc x y = Lg C2 (variant C0 x y).
Proof. by []. Qed.

Lemma variant_V_ca x y:  Vg (variantLc x y) C0 = x.
Proof. by rewrite  LgV ;[ apply: variant_true |fprops]. Qed.

Lemma variant_V_cb x y:  Vg (variantLc x y) C1 = y.
Proof. rewrite LgV;[ apply: variant_false | ] ;fprops.  Qed.

Hint Rewrite variant_V_ca variant_V_cb: aw.

Ltac try_lvariant u:=  move:u;move/C2_P; case => ->; aw.


Lemma variant_true1 x y: variant C0 x y C0 = x.
Proof. by rewrite variant_true.  Qed.

Lemma variant_false1 x y: variant C0 x y C1 = y.
Proof. rewrite variant_false; fprops. Qed.

Hint Rewrite variant_true1 variant_false1 : aw.

Lemma variantLc_comp a b f:
 variantLc (f a) (f b) = 
  Lg (domain (variantLc a b))(fun z => f (Vg (variantLc a b) z)).
Proof.
apply: fgraph_exten;aww.
move=> x xtp; try_lvariant xtp; rewrite LgV; aww.
Qed.


Lemma set2_equipotent_aux x y 
   (g := (Lf (variant x C0 C1) (doubleton x y) C2)): x <> y ->
  [/\ bijection_prop g (doubleton x y) C2, Vf g x = C0 & Vf g y = C1].
Proof.
move => neq.
have ax: lf_axiom (variant x C0 C1) (doubleton x y) C2.
   by rewrite /variant;move => t tp; apply /set2_P; Ytac h; [left | right].
rewrite ! LfV;fprops; rewrite /variant; Ytac0; Ytac0; split => //.
rewrite /g/variant;saw;apply: lf_bijective => //.
  move=> u v /set2_P [] -> /set2_P [] -> //; Ytac0 => //; Ytac0 => // => h.
  - by case: C0_ne_C1.
  - by case: C1_ne_C0.
by move => z; case/C2_P => ->; [exists x | exists y]; fprops; Ytac0.
Qed.


Lemma Eq_set2_C2 x y:  x <> y -> doubleton x y \Eq C2.
Proof.
move => h; move:(set2_equipotent_aux h); set g := Lf _ _ _.
move =>[gp _ _]. apply: (equipotent_bp gp).
Qed.

Proof.
(** We have a partition of a set by selecting a subset and its complement *)

Definition partition_with_complement x j := 
  variantLc j (x -s j).

Lemma is_partition_with_complement x j:
  sub j x -> partition_w_fam (partition_with_complement x j) x.
Proof. 
rewrite /partition_with_complement=> jx; split.
- by apply: variantLc_fgraph.
- move=> a b; aw;case /C2_P => -> ;case /C2_P => ->; fprops;
  right; aw; [ |  apply (disjoint_S)];apply:set_I2Cr. 
- by rewrite/unionb /variantLc variant_d setUf2f; aw; apply:setU2_Cr.
Qed.

Lemma union2Lv a b: a \cup b = unionb (variantLc a b).
Proof.
rewrite/unionb;aw; rewrite setUf2f.
by rewrite  variant_V_ca variant_V_cb.  
Qed.

Lemma disjointLv a b: disjoint a b -> 
   mutually_disjoint (variantLc a b).
Proof.
move=> db i j; aw => id1 jd; try_lvariant id1; try_lvariant jd; fprops.
by right;apply:disjoint_S.
Qed.

Lemma partition_setU2 A B (f: fterm): disjoint A B ->
   partition_w_fam (variantLc A B) (domain (Lg (A \cup B) f)).
Proof.
aw; hnf; rewrite union2Lv;split; fprops.
move => i j; aw; case/C2_P => ->; case/C2_P => ->; aww.
by right; apply: disjoint_S.
Qed.


Lemma mutually_disjoint_prop3 D f:
  mutually_disjoint (Lg D (fun i => f i *s1 i)).
Proof.
apply: mutually_disjoint_prop2; move=> u v  y _ _. 
by move=> /setX_P [_ _ /set1_P <-] /setX_P [_ _ /set1_P <-]. 
Qed.

(** Greatest and least partition for covering order*)

Definition greatest_partition x :=  fun_image x singleton. 
Definition least_partition x := (singleton x).

Lemma least_is_partition x:
   nonempty x -> partition_s (least_partition x) x.
Proof. 
rewrite /least_partition=>ne.
split; last by move=> a /set1_P ->.
split; first by apply: setU_1.
by move=> a b /set1_P -> /set1_P ->; left.
Qed.

Lemma greatest_partition_P x z:
  inc z (greatest_partition x) <-> exists2 w, inc w x & z = singleton w .
Proof. apply/funI_P. Qed.

Lemma greatest_is_partition x: partition_s (greatest_partition x) x.
Proof. 
split; last by move=> a /greatest_partition_P [w wx ->]; apply: set1_ne.
split.
  set_extens t.
    move /setU_P => [y yt /greatest_partition_P [w wx swy]].
    by move: yt; rewrite swy; move/set1_P => ->.
  move=> tx; apply/setU_P;exists (singleton t); fprops.
  apply /greatest_partition_P; ex_tac. 
move=> a b/greatest_partition_P [w wx] -> /greatest_partition_P [w' wx'] ->.
mdi_tac ww => u /set1_P -> /set1_P sw; case: ww; ue.
Qed.

(** A strict partition is an injective functional graph *)

Definition injective_graph f:=
  fgraph f /\  {inc domain f &, injective (Vg f)}.

Lemma injective_partition f x:
  partition_s_fam f x -> injective_graph f.
Proof.
move=> [[fgf md ux] hyp]; split=>//.
move=> a b ad bd sV; move: (md _ _ ad bd) (hyp _ bd)=> [] //.
rewrite /disjoint sV setI2_id => -> [_ [[]]]. 
Qed.

Lemma partition_fam_partition f x:
  partition_s_fam f x -> partition_s (range f) x.
Proof. 
move=> [pf hyp]; move: (partition_same2 pf)=> [ur di].
move:pf=> [fgf md _]; split=>//. 
move=> a /(rangeP (proj1 fgf)) [b bf]; move: (pr2_V fgf bf); aw => ->. 
apply: hyp;ex_tac.
Qed.

Lemma inv_image_disjoint g : function g -> 
  {compat (Vfi g) : x y / disjoint x y}.
Proof.
move=> fg x y dxy; rewrite /disjoint -iim_fun_setI2 //.
by apply /set0_P => t /iim_fun_P [u]; rewrite dxy => /in_set0. 
Qed.

(** Given a partition, a function on each subset can be uniquely extended; 
 We give two variants, in one case the targets may be different *) 

Lemma extension_partition_aux f x t h:
  partition_w_fam f x -> 
  (forall i, inc i (domain f) -> function_prop (h i) (Vg f i) t) ->
  (forall i j, inc i (domain f) -> inc j (domain f) ->
    agrees_on ((Vg f i) \cap (Vg f j)) (h i) (h j)).
Proof.
move=> [fgf mdf ufx] afp.
move=> i j id jd; case: (mdf _ _ id jd).
  move=> ->; rewrite setI2_id; move: (afp _ jd)=> [_ shj _].
  hnf; rewrite shj; split;fprops => s //.
rewrite/disjoint=> ->; hnf; split; try split; fprops.
by move=> a /in_set0.
Qed.

Lemma extension_partition1 f x t h (g := common_ext f h t):
  partition_w_fam f x -> 
  (forall i, inc i (domain f) -> function_prop (h i) (Vg f i) t) ->
  (function_prop g x t /\
    (forall i, inc i (domain f) -> agrees_on (Vg f i) g (h i))).
Proof.
move => pfa afp.
move: (extension_covering afp (extension_partition_aux pfa afp)).
by move: pfa => [fgf mdf ufx]; rewrite -/g - ufx; move => [h1 _ h2 h3].
Qed.

Lemma extension_partition2 f x t h
  (g:= common_ext f (fun i => (triple (Vg f i) t (graph (h i)))) t):
  partition_w_fam f x -> 
  (forall i, inc i (domain f) -> function_prop_sub (h i) (Vg f i) t) ->
  ( function_prop g x t /\
    forall i, inc i (domain f) -> agrees_on (Vg f i) g (h i)).
Proof.
move=> pf prop.
pose nh i := triple (Vg f i) t (graph (h i)).
have afp: forall i, inc i (domain f) -> function_prop (nh i) (Vg f i) t. 
  move=> i id; move: (prop _ id) => [fgh sg th];rewrite /nh. 
  saw; apply: function_pr; fprops.
    by apply: sub_trans th; apply: f_range_graph.
  by rewrite domain_fg.
have [fpg aag] := (extension_partition1 pf afp). 
split=>// => i idf; move: (aag _ idf)=> [aa cc bb];split=>//.
  by move: (prop _ idf) => [_ -> _]; fprops.
by move=> a aV; rewrite /g /nh (bb _ aV) /nh /Vf; aw.
Qed.

Theorem extension_partition_thm f x t h:
  partition_w_fam f x -> 
  (forall i, inc i (domain f) -> function_prop (h i) (Vg f i) t) ->
  exists! g, (function_prop g x t /\
    (forall i, inc i (domain f) -> agrees_on (Vg f i) g (h i))).
Proof.
move => pfa afp.
have aah:= (extension_partition_aux pfa afp).
move: pfa => [fgf mdf <-]; exact: (extension_covering_thm afp aah fgf). 
Qed.


(** ** EII-4-8 Sum of a family of sets  *)


(** Given a family [X], we construct a family [Y] that satisfies 
  the previous theorem; the [unionb Y] is called the disjoint union *)

Definition disjointU_fam f := Lg (domain f)(fun i => (Vg f i) *s1 i).
Definition disjointU f :=  unionb (disjointU_fam f).

Lemma disjointU_disjoint f:
  mutually_disjoint (disjointU_fam f).
Proof. 
move=> i j; rewrite  Lgd=> id jd ;rewrite ! LgV //.
by mdi_tac t => u /indexed_P [_ _] qu /indexed_P [_ _]; rewrite qu.
Qed.

Hint Resolve disjointU_disjoint: fprops.

Lemma disjointU_fgraph f: fgraph (disjointU_fam f).
Proof. rewrite /disjointU_fam; fprops. Qed.

Lemma disjointU_d f: domain (disjointU_fam f) = domain f.
Proof. by rewrite /disjointU_fam; aw. Qed.

Hint Resolve  disjointU_fgraph: fprops.


Lemma disjointU_E I (f:fterm ):
  disjointU (Lg I f) = unionf I (fun i : Set => f i *s1 i).
Proof.
rewrite /disjointU/disjointU_fam/unionb; aw.
by apply: setUf_exten => i iI; rewrite !LgV.
Qed.


Theorem disjoint_union_lemma f:
  exists g x,
    [/\ fgraph g, x = unionb g,
    (forall i, inc i (domain f) -> (Vg f i) \Eq (Vg g i))
    & mutually_disjoint g].
Proof.
exists (disjointU_fam f), (disjointU f); split;fprops.
move=> i idf; rewrite LgV//; apply:Eq_indexed.
Qed.

Lemma partition_disjointU f:
  partition_w_fam (disjointU_fam f) (disjointU f).
Proof. 
split; [fprops | by apply: disjointU_disjoint | done ].
Qed.

Lemma disjointU_hi f x: inc x (disjointU f) ->
  [/\ inc (Q x) (domain f), inc (P x) (Vg f (Q x)) & pairp x].
Proof. 
move/setUb_P => [t]; rewrite disjointU_d => td.
by rewrite LgV //; move /indexed_P => [pa pb ->]. 
Qed. 

Lemma disjointU_P f x: inc x (disjointU f) <->
  [/\ inc (Q x) (domain f), inc (P x) (Vg f (Q x)) & pairp x].
Proof. 
split; first by apply: disjointU_hi.
move => [pa pb pc]; apply/setUb_P; rewrite disjointU_d; ex_tac.
rewrite LgV //; rewrite - {1} pc; apply/setXp_i; fprops.
Qed. 

Lemma disjointU_pi f x y:
  inc y (domain f) -> inc x (Vg f y) ->
  inc (J x y) (disjointU f).
Proof. move => ta tb;apply/disjointU_P; aw; split; fprops. Qed.

Lemma disjointU2_rw a b x y:  y <> x ->
  disjointU (variantL x y a b) = (a *s1 x) \cup (b *s1 y).
Proof.
move=> yx.
rewrite/disjointU /disjointU_fam.
have -> : domain (variantL x y a b) = doubleton x y by rewrite/ variantL; aw.
set_extens z.
  move/setUb_P; aw; move => [u ud]; rewrite LgV //; move/setX_P => [pz Pz Qz].
  rewrite -pz; move/set1_P: Qz ->; apply/setU2_P; move: Pz.
  case /set2_P: ud=> ->;  rewrite ?variant_V_a ? (variant_V_b _ _ yx);
    [left | right]; apply: setXp_i => //; fprops.
move=> h.
have Qz: (inc (Q z) (doubleton x y)).
  case /setU2_P :h => /setX_P [_ _] /set1_P ->; fprops.
apply/setUb_P; aw; exists (Q z) => //; rewrite LgV //. 
by case/setU2_P: h => /setX_P [pz Pz w]; move/set1_P: (w) ->; 
  apply: setX_i; fprops; rewrite ?variant_V_a ? variant_V_b.
Qed.

Lemma disjointU2_rw1 a b:
  disjointU (variantLc a b) =  (a *s1 C0) \cup (b *s1 C1).
Proof. rewrite/variantLc disjointU2_rw //; fprops. Qed.

(** There is a canonical mapping from the disjoint union onto the union; It is bijective if the family is disjoint *)

Theorem disjointU_pr f
  (h := fun i => Lf P  ((Vg f i) *s1 i) (unionb f))
  (g := common_ext (disjointU_fam f) h (unionb f)):
  [/\ source g = disjointU f,
    target g = unionb f,
    surjection g &
    (mutually_disjoint f -> bijection g)].
Proof. 
set aux:= (Lg (domain f) (fun i => (Vg f i) *s1 i)).
have pf:= (partition_disjointU f).
have da: (domain aux = domain f) by rewrite /aux; aw.  
have tap: forall i, inc i (domain aux) -> lf_axiom P ((Vg f i) *s1 i)(unionb f).
  by move => i id x; move/setX_P=> [_ pv Qi];  union_tac; ue.
have fpi: (forall i, inc i (domain aux) -> 
    function_prop (h i) (Vg aux i)(unionb f)). 
  move=> i id; split. 
  + by apply: lf_function;apply: tap. 
  + rewrite lf_source LgV //; ue.
  + by rewrite lf_target.
move:(extension_partition1 pf fpi).
rewrite -/g; move => [fpg aag].
move: aag; aw; rewrite/disjointU_fam; aw => aag.
have [fg sg tg] := fpg.
have sug: (surjection g).
  apply: surjective_pr5=>//; rewrite /related tg sg. 
  move=> y; move /setUb_P=> [z zdf yg].
  set (t:= J y z).
  have tsg: inc t (disjointU f) by rewrite /t; apply: disjointU_pi.
  have ps: inc t ((Vg f z) *s1 z) by rewrite /t/indexed ; aww.
  exists t => //.
  suff: y = Vf g t by move=>->; apply: Vf_pr3 =>//; rewrite sg.
  move: (proj33 (aag _ zdf)); rewrite LgV // => sv.  
  by rewrite (sv _ ps) LfV //; [ rewrite/t;aw |  by apply: tap; ue].
split=>//.
move=> mf; split=>//; split => //.
rewrite sg => x y xsg ysg.
have [qxd pV xp]:= (disjointU_hi xsg).
have  [qyd pyV yp] := (disjointU_hi ysg).
move: (aag _ qxd); rewrite (LgV qxd) => - [ _ _ ax].
move: (aag _ qyd). rewrite (LgV qyd) => - [ _ _ ay].
have xs: inc x ((Vg f (Q x)) *s1 (Q x)) by apply: setX_i; fprops.
have ys: inc y ((Vg f (Q y)) *s1 (Q y)) by apply: setX_i; fprops.
rewrite (ax _ xs) (ay _ ys).
have ax2: lf_axiom P (Vg f (Q x) *s1 Q x) (unionb f). apply: tap; ue.
have ax3: lf_axiom P (Vg f (Q y) *s1 Q y) (unionb f). apply: tap; ue.
rewrite !LfV => // sp.
move: (mf _ _  qxd qyd); case => sa; first by apply: pair_exten.
by empty_tac1 (P x); rewrite sp.
Qed.

Definition canonical_du2 a b := disjointU (variantLc a b).

Lemma candu2_rw a b:
  canonical_du2 a b = (a *s1 C0) \cup (b *s1 C1).
Proof. by rewrite /canonical_du2 disjointU2_rw1. Qed.

Lemma candu2P a b x:
  inc x (canonical_du2 a b) <-> (pairp x /\ 
  ((inc (P x) a /\ Q x = C0) \/ (inc (P x) b /\ Q x = C1))).
Proof. 
rewrite candu2_rw; split.
  case /setU2_P; move /indexed_P => [pa pb];  fprops.
by move => [pa [] [h1 h2]]; apply/setU2_P; [left | right ]; apply /indexed_P.
Qed.

Lemma candu2_pr2 a b x:
  inc x (canonical_du2 a b) -> (Q x = C0 \/ Q x = C1).
Proof. by move /candu2P => [_]; case => [] [_]; [left | right]. Qed.

Lemma candu2_pra a b x: 
  inc x a -> inc (J x C0) (canonical_du2 a b).
Proof. by move=> xa; apply /candu2P; split;fprops; left; aw. Qed.

Lemma candu2_prb a b x:
  inc x b -> inc (J x C1) (canonical_du2 a b).
Proof. by move => xb; apply /candu2P; split; fprops ; right; aw. Qed.


Notation  dsum:= canonical_du2.


Lemma disjointU2_pr0 a b x y:
  disjoint x y -> disjoint (a \times x) (b \times y).
Proof. 
move=> dxy; apply: disjoint_pr. 
move=> u /setX_P [_ _ qx] /setX_P [_ _ qy].
apply: (nondisjoint qx qy dxy).
Qed.

Lemma disjointU2_pr1 x y:
  x <> y -> disjoint (singleton x) (singleton y).
Proof. by move=> xy;apply: disjoint_pr; move => u /set1_P -> /set1_P. Qed.

Lemma disjointU2_pr a b x y:
  x <> y ->  disjoint (a *s1 x) (b *s1 y).
Proof. by move=> xy; apply: disjointU2_pr0; apply: disjointU2_pr1. Qed.

Hint Resolve disjointU2_pr: fprops.


Lemma Eq_du2 a b a' b' : disjoint a b ->  disjoint a' b' -> 
  a \Eq a' -> b \Eq b' -> (a \cup b) \Eq (a' \cup b').
Proof.
move => du1 du2 [f [[[ff fi] [_ fs]] sf tf]] [g [[[fg gi] [_ gs]] sg tg]].
pose h x := Yo (inc x a) (Vf f x) (Vf g x).
exists (Lf h (a \cup b) (a' \cup b')); saw.
rewrite sf in fi fs; rewrite sg in gi gs;rewrite tf in fs; rewrite tg in gs.
have Ha x: inc x b -> ~ inc x a by clear du2;move => ba bb; empty_tac1 x.
rewrite /h;apply: lf_bijective.
- move =>x /setU2_P; case  => xa; first by Ytac0; apply:setU2_1; Wtac.
  move: (Ha x xa) => wb; Ytac0;apply:setU2_2; Wtac.
- move => u v; case/setU2_P => ua; case/setU2_P => va. 
  + by Ytac0; Ytac0; apply: fi.
  + move: (Ha _ va) => wb; Ytac0; Ytac0 => sv.
    empty_tac1  (Vf f u); [ Wtac |  rewrite sv;Wtac].
  + move: (Ha _ ua) => wb; Ytac0; Ytac0 => sv.
    empty_tac1  (Vf g u); [ rewrite sv; Wtac |  Wtac].
  + by move: (Ha _ ua)  (Ha _ va)=> ub bv; Ytac0; Ytac0; apply: gi.
move => y /setU2_P; case => ya.
  by move:(fs _ ya) =>[x xqa ->]; exists x; fprops; Ytac0.
by move:(gs _ ya) =>[x xqa ->]; exists x; fprops; rewrite Y_false => //;case/Ha.
Qed.

Lemma Eq_ii1 A i j: (A *s1 i) \Eq (A *s1 j).
Proof. exact: (EqT (EqS (Eq_indexed A i)) (Eq_indexed A j)). Qed.

Lemma Eq_ii2 A B i j: A \Eq B -> (A *s1 i) \Eq (B *s1 j).
Proof.
move => h; exact: (EqT (EqT (EqS (Eq_indexed A i)) h) (Eq_indexed B j)).
Qed.

Lemma dsum_same x: dsum x x = x \times C2.
Proof. by rewrite candu2_rw - set2_UXr setU2_11. Qed.

Lemma Eq_C1uC1_C2: C2 \Eq dsum C1 C1.
Proof. rewrite dsum_same;  apply: Eq_rindexed.   Qed.

Lemma Eq_sum_inv A B C D: A \Eq B -> C \Eq D -> dsum A C \Eq dsum B D.
Proof.
move:C0_ne_C1 C1_ne_C0 => ha hb sa sb; rewrite ! candu2_rw.
by apply: Eq_du2; fprops;  apply:Eq_ii2.
Qed.


Lemma Eq_sumC A B: dsum A B \Eq dsum B A.
Proof.
move:C0_ne_C1 C1_ne_C0 => ha hb; rewrite ! candu2_rw setU2_C.
apply: Eq_du2; fprops ;apply: Eq_ii1.
Qed.

Lemma Eq_sumA a b c: dsum a (dsum b c) \Eq (dsum (dsum a b) c).
Proof. 
move: a b c.
have aux: (forall u v w  a b c,  v <> u-> u <> w -> w <> v -> 
  dsum a (dsum b c) \Eq ((a *s1 u) \cup  ((b *s1 v) \cup (c  *s1  w)))).
  move=> u v w a b c vu uw wv.
  rewrite  !candu2_rw; apply:Eq_du2; fprops.
      apply: disjoint_pr; move=> z; move/setX_P => [_ _ /set1_P pa]
      /setU2_P [] /setX_P [_ _ /set1_P]; rewrite pa => //; apply:nesym => //.
    apply: Eq_ii1.
  apply: (EqT (EqS (Eq_indexed ((b *s1 C0) \cup (c *s1 C1))  C1))).
  by apply:Eq_du2; fprops; apply: Eq_ii1.
move: C2_ne_C01 => [/nesym ne3 ne2] a b c.
move:(aux _ _ _ a b c C1_ne_C0  ne3 ne2) (aux _ _ _ c a b ne3 ne2 C1_ne_C0 ).
rewrite setU2_A setU2_C => s1 s2.
exact: (EqT (EqT s1 (EqS s2)) (Eq_sumC c (dsum a b))).
Qed.


Lemma Eq_muldr a b c: 
  a \times dsum b c \Eq dsum (a \times b) (a \times c).
Proof.
rewrite ! candu2_rw set2_UXr; apply: Eq_du2; try apply:Eq_mulA.
  apply: disjointU2_pr0;apply: disjointU2_pr; fprops.
apply: (disjointU2_pr);  fprops.
Qed.


(** * EII-5 Product of a family of sets *)
(** ** EII-5-1 The axiom of the set of subsets *)

(** Bourbaki has an axiom (not needed here) that says that the powerset exists *)

(** Canonical extension of [f:E->F] to [\Po E -> \Po F]*) 

Definition extension_to_parts f :=
  Lf (Vfs f) (\Po (source f)) (\Po (target f)).

Notation "\Pof f" :=   (extension_to_parts f) (at level 40).  

Lemma etp_axiom f: correspondence f ->
  lf_axiom (Vfs f) (\Po (source f)) (\Po (target f)).
Proof.
move=> cf x /setP_P xs; apply/setP_P.
apply: (@sub_trans (range (graph f))); fprops; apply: dirim_Sr.
Qed.

Lemma etp_f f: correspondence f -> function (\Pof f).
Proof. 
by move => cf; apply: lf_function;apply: etp_axiom.
Qed.

Lemma etp_V f x:
  correspondence f -> sub x (source f) -> Vf (\Pof f) x = Vfs f x.
Proof. 
by move => cf /setP_P s; rewrite LfV //; apply: etp_axiom.
Qed.

Hint Resolve etp_f : fprops.

(** Morphism properties of extension *)

Lemma etp_composable f g:  composableC g f ->   (\Pof g) \coP (\Pof f).
Proof.   
move=> [cf cg cfg]; split; fprops. 
rewrite /extension_to_parts;aw; ue.
Qed. 


Lemma etp_coP f g : g \coP f -> (\Pof g) \coP (\Pof f).
Proof.
move => [ha hb hc];split => //.
- by apply: etp_f; case: ha.
- by apply: etp_f; case: hb.
- by rewrite /extension_to_parts; aw; rewrite hc.
Qed.

Lemma etp_compose:
  {when: composableC, {morph extension_to_parts: x y / x \co y }}.
Proof. 
move=> g f /= cgf; symmetry.
have cegf:= (etp_composable cgf).
have [cf cg cfg] := cgf.
have ccg: (correspondence (g \co f)) by apply: compf_correspondence.
apply: function_exten; try fct_tac; fprops;
  try  solve[rewrite /extension_to_parts ; aw; trivial].
aw; move => x xs.
move: (xs). rewrite lf_source  => /setP_P xs1.
have xs2: sub x (source (g \co f)) by aw.
rewrite compfV // ! etp_V //.
  by rewrite /compose/Vfs; aw; symmetry; apply:compg_image. 
rewrite cfg; apply: (@sub_trans (range (graph f))); fprops.
apply: dirim_Sr.
Qed.

Lemma etp_identity x: \Pof (identity x) = identity (\Po x).
Proof. 
have ic:=(@identity_corresp x).
apply: function_exten; fprops.
    by rewrite/extension_to_parts; aw.
  by rewrite/extension_to_parts; aw.
move=> y /=; rewrite {1} /extension_to_parts; aw => ys1.
move /setP_P: (ys1) => ys2. 
have ys: sub y (source (identity x)) by aw; apply/setP_P.
have fi: (function (identity x)) by fprops.
rewrite etp_V // idV //; set_extens t.
  by move /(Vf_image_P fi ys)=> [u uy]; rewrite idV; [ move=> -> | apply: ys2].
by move => ty;apply /(Vf_image_P fi ys); ex_tac; rewrite idV //; apply: ys2.
Qed.

Lemma composable_for_function f g:
  g \coP f -> composableC g f.
Proof. by move=>  [[ fg _ _] [ff _ _ ] eq].  Qed.

Theorem etp_fs f: surjection f -> surjection (\Pof f).
Proof.
move=> sf; apply: surj_if_exists_right_inv. 
have [r [cfr cfri]]:= (exists_right_inv_from_surj sf).
have cfr' := (composable_for_function cfr).
exists (extension_to_parts r); split; first by apply: etp_composable.  
by rewrite - etp_compose // cfri etp_identity /extension_to_parts; aw.
Qed.

Theorem etp_fi f: injection f -> injection (\Pof f).
Proof.
move=> inf.
case: (emptyset_dichot (source f))=> eq.
  move: inf=> [[ cf _] _]; split; fprops. 
  rewrite {1 2} /extension_to_parts=> x y.
  by rewrite lf_source eq setP_0; move /set1_P => -> /set1_P ->. 
have [r [cfr cfri]] := (exists_left_inv_from_inj inf eq).
have cfr' := (composable_for_function cfr).
apply: inj_if_exists_left_inv. 
exists (extension_to_parts r); split; first by apply: etp_composable.  
by rewrite - etp_compose // cfri etp_identity /extension_to_parts; aw.
Qed.


Lemma etp_inv f (g := (\Pof f)):  bijection f ->
  bijection g /\ (inverse_fun g) = \Pof (inverse_fun f).
Proof.
move => bf.
have bg: bijection g. 
  split; [ exact(etp_fi (proj1 bf)) | exact(etp_fs (proj2 bf)) ].
split => //. 
move:(bij_right_inverse bf) => /(f_equal extension_to_parts).
have ha:=(composable_for_function (composable_f_inv bf)).
have hb:  g \coP extension_to_parts (inverse_fun f).
  split; [ fct_tac | |  by rewrite /g /extension_to_parts; aw]. 
  apply:(etp_f (proj31 ha)).
rewrite (etp_compose ha) etp_identity -/g => hh.
apply:(bijection_inverse_aux bg) => //.
by rewrite hh /extension_to_parts; aw.
Qed.

(** ** EII-5-2 Set of mappings of one set into another *)

(** The set of functional graphs is denoted by  F^E, the set of functions by calF(E; F)*) 

Definition functions x y :=
  Zo (correspondences x y)
  (fun z => fgraph (graph z) /\ x = domain (graph z)).
Definition permutations E := 
  Zo (functions E E) bijection.
Definition bijections x y := Zo (functions x y) bijection.

Definition sub_functions x y :=
  unionf(\Po x)(functions ^~ y).

Lemma functionsP x y f:
  inc f (functions x y) <-> (function_prop f x y).
Proof. 
rewrite/function; split.
  move/Zo_P => [/correspondences_P [p1 p2 p3] [p4 p5]]; split => //. 
  split => //; ue.
by move=> [[qa qb qc] <- pc]; apply: Zo_i; [apply/correspondences_P | split].
Qed.

Lemma permutationsP x E: inc x (permutations E) <-> bijection_prop x E E.
Proof.
split; first by move => /Zo_P [/functionsP [pa pb pc] pd]. 
move => [pa pb pc]; apply:Zo_i => //; apply/functionsP; split => //; fct_tac.
Qed.


Lemma bijectionsP x y f: inc f (bijections x y) <-> bijection_prop f x y.
Proof.
split.
   by move /Zo_P => [/functionsP [_ sf tf]] bf.
move=> [fa fb fc]; apply:Zo_i => //; apply /functionsP; split => //; fct_tac.
Qed.


Lemma etp_fun A B f: inc f (functions A B) -> 
  inc (\Pof f) (functions (\Po A) (\Po B)).
Proof.
move/functionsP => [ff st tf]; apply /functionsP; split.
- by apply: etp_f; case ff.
- by rewrite /extension_to_parts - st; aw.
- by rewrite /extension_to_parts - tf; aw.
Qed.

Lemma etp_bij A B f: inc f (bijections A B) -> 
  inc (\Pof f) (bijections (\Po A) (\Po B)).
Proof.
move /bijectionsP => [bf sd tf].
have: inc f (functions A B) by apply/functionsP; split => //; fct_tac.
move /etp_fun =>/functionsP [_ sf' st'].
apply/bijectionsP; split => //.
split;[ apply: (etp_fi (proj1 bf)) | apply: (etp_fs (proj2 bf))].
Qed.

Lemma etp_comp A B C f g: inc f (functions A B) -> inc g (functions B C) -> 
  \Pof (g \co f)  = (\Pof g) \co (\Pof f).
Proof.
move /functionsP => [[ff _ _] _ tf ] /functionsP [[fg _ _ ] sg _].
have cc: source g = target f by ue.
by apply:(etp_compose). 
Qed.


Lemma ext_to_prod_fun A B A' B' f g:
  inc f (functions A B) -> inc g (functions A' B') ->
  inc (f \ftimes g) (functions (A \times A') (B \times B')).
Proof.
move => /functionsP [ff sf tf] /functionsP [fg sg tg].
apply/functionsP; split.
- by apply:ext_to_prod_f.
- by rewrite /ext_to_prod; rewrite sf sg; aw.
- by rewrite /ext_to_prod; rewrite tf tg; aw.
Qed.

Lemma ext_to_prod_fun_bis A B A' B' f g:
  function_prop f A B -> function_prop g A' B' ->
  function_prop (f \ftimes g)  (A \times A') (B \times B').
Proof.
move => /functionsP ha /functionsP hb. 
by apply/functionsP /ext_to_prod_fun.
Qed.

Lemma ext_to_prod_bij A B A' B' f g:
  inc f (bijections A B) -> inc g (bijections A' B') ->
  inc (f \ftimes g) (bijections (A \times A') (B \times B')).
Proof.
move => /bijectionsP [ff sf tf] /bijectionsP [fg sg tg].
apply/bijectionsP; split.
- by apply: ext_to_prod_fb.
- by rewrite /ext_to_prod; rewrite sf sg; aw.
- by rewrite /ext_to_prod; rewrite tf tg; aw.
Qed.

Lemma ext_to_prod_comp A B C A' B' C' f g f' g':
  inc f (functions A B) -> inc f' (functions A' B') ->
  inc g (functions B C) -> inc g' (functions B' C') ->
  (g \ftimes g') \co (f \ftimes f') = (g \co  f) \ftimes (g' \co f').
Proof.
move => /functionsP[ff _ tf]/functionsP[ff' _ tf'].
move => /functionsP[fg sg _]/functionsP[fg' sg' _].
apply: compose_ext_to_prod2; split => //; ue.
Qed.


Lemma inverse_bij_bp g E E': 
  (bijection_prop g E E') ->  bijection_prop (inverse_fun g) E' E.
Proof.
by move => [pa pb pc];hnf; aw; split => //; apply: inverse_bij_fb.
Qed.

Lemma compose_bp E E' E'' g g': 
  bijection_prop g E E' -> bijection_prop g' E' E'' -> 
  bijection_prop (g' \co g) E E''.
Proof. 
move=> [ha1 ha2 ha3] [hb1 hb2 hb3]. 
hnf; aw;split => //; apply: compose_fb => //; split; try fct_tac.
by rewrite ha3.
Qed.



Definition gfunctions x y:=
  Zo (\Po (x \times y))(fun z => fgraph z /\ x = domain z).

Lemma sfunctionsP x y f:
  inc f (sub_functions x y) <->
  [/\ function f, sub (source f) x & target f = y].
Proof.
split.
  move/setUf_P => [z /setP_P zx /functionsP [pa pb pc]];split => //; ue.
by move => [pa /setP_P pb pc]; apply /setUf_P; ex_tac; apply/functionsP.
Qed.

Lemma gfunctions_i f:
  function f -> inc (graph f) (gfunctions (source f) (target f)).
Proof. by move=> [[pa pd] pb pc]; apply: Zo_i => //; apply/setP_P. Qed.

Lemma gfunctions_i1 f E F: lf_axiom f E F ->
  inc (Lg E f) (gfunctions E F).
Proof. by move =>/ lf_function/gfunctions_i; rewrite /Lf; aw. Qed.

Lemma gfunctions_hi x y z:
  inc z (gfunctions x y) -> exists f,
    [/\ function  f,  source f = x, target f = y & graph f = z].
Proof.
move/Zo_P => [/setP_P /corr_propcc [_ _ pa] [pb pc]].
exists (triple x y z); aw; split => //; apply: function_pr=>//. 
Qed.

Lemma function_exten5 x y a b:
  inc a (functions x y) -> inc b (functions x y) ->
  graph a = graph b -> a = b.
Proof. 
move /functionsP=> [fa sa ta] /functionsP [fb sb tb] sg.
apply: function_exten1=>//; ue.
Qed.

Lemma functions_empty X:
   functions emptyset X = singleton (empty_function_tg X).
Proof.
move: (empty_function_tg_function X) => h.
apply: set1_pr; first by apply /functionsP.
move: h =>  [fa sa ta].
move => z /functionsP  [ft st tt];  apply: function_exten => //; try ue.
by rewrite st => x /in_set0.
Qed.

Lemma fun_set_small_source y:  small_set (functions emptyset y).
Proof. by rewrite functions_empty; apply: small1. Qed.

Lemma fun_set_small_target x:  small_set (functions x emptyset).
Proof.
move=> u v uf vf; apply: (function_exten5 uf vf).
move /functionsP: uf => [fa _ ta]; move/functionsP: vf => [fb _ tb].  
rewrite !empty_target_graph//. 
Qed.

Lemma fun_set_ne x y: (x = emptyset \/ nonempty y) -> nonempty (functions x y).
Proof. 
case=> p. 
  rewrite p;move: (empty_function_tg_function y) => h.
  by exists (empty_function_tg y); apply/functionsP.
move: p => [p py]; exists (constant_function x y p); apply/functionsP.
by apply constant_prop.
Qed.



Lemma empty_function_bf: bijection_prop empty_function emptyset emptyset.
Proof.
have [p1 p2 p3]:= empty_function_function.
split => //; split;split => //.
  by move => x y; rewrite p2 => /in_set0.
by move => y; rewrite p3 => /in_set0.
Qed.

(** Canonical isomorphism between calF(E,F)  and F^E *)

Lemma graph_lf_axiom x y:
  lf_axiom graph (functions x y) (gfunctions x y).
Proof. by move=> g /functionsP [fg <- <-]; apply: gfunctions_i. Qed.

Lemma graph_fb x y:
  bijection (Lf graph (functions x y) (gfunctions x y)).
Proof. 
apply: lf_bijective.
- by apply: graph_lf_axiom.
- by move=> u v us vs g; apply: (function_exten5 us vs g).  
- move=> z /gfunctions_hi  [f [pa pb pc pd]].
  by exists f => //;apply/functionsP.
Qed.

Lemma Eq_fun_set x y:  (functions x y) \Eq (gfunctions x y).
Proof. apply: (equipotent_aux (f:= graph)); aw; apply: graph_fb. Qed.

(** Isomorphism between calF(E,F) and calF(E',F')  for equipotent sets *)

Definition compose3function u v :=
  Lf (fun f =>  (v \co f) \co u)
  (functions (target u) (source v))
  (functions (source u) (target v)).

Lemma c3f_axiom u v:
  function u -> function v -> 
  lf_axiom (fun f =>  (v \co f) \co u)
  (functions (target u) (source v))
  (functions (source u) (target v)).
Proof.
move=> fu fv x => /functionsP [fx sx tx]; apply/functionsP; hnf; aw.
by split=> //; fct_tac ;[fct_tac | aw].
Qed.

Lemma c3f_f u v:
  function u -> function v -> function (compose3function u v).
Proof. by move =>fu fv; apply: lf_function; apply: c3f_axiom. Qed.

Lemma c3f_V u v f:
  function u -> function v -> 
  function f -> source f = target u -> target f = source v ->
  Vf (compose3function u v) f = (v \co f) \co u.
Proof. 
move => fu fv ff sf tf.
rewrite LfV //; [apply: c3f_axiom=>// | by apply/functionsP]. 
Qed.

Theorem c3f_fi u v:
  surjection u -> injection v -> injection (compose3function u v).
Proof. 
rewrite /compose3function=> su iv.
have fu: function u by fct_tac.
have fv: function v by fct_tac. 
apply: lf_injective; first by apply: c3f_axiom.
move=> f g. 
case: (emptyset_dichot (source v)) => sve. 
  by move=> i1 i2 c; apply: (fun_set_small_target (x:= target u)); ue. 
have [s [cus cusi]] := (exists_right_inv_from_surj su).
move: (exists_left_inv_from_inj iv sve). 
move=> [r [crv crvi]] /functionsP [ff sf tf] /functionsP [fg sg tg].
have cvf: v \coP f by [].
have cvg: v \coP g by [].
have fvf: function (v \co f) by fct_tac.
have fvg: function (v \co g) by fct_tac.
have cvfu: (v \co f) \coP u by hnf; aw.
have cvgu: (v \co g) \coP u  by hnf; aw.
move/(congr1 (fun  i => i \co s)).
rewrite - compfA // cusi - sf - (compf_s f v) compf_id_r //.
rewrite - compfA // cusi - sg - (compf_s g v) compf_id_r //.
move /(congr1  (fun  i => r \co i)). 
rewrite compfA // crvi - tf compf_id_l // compfA // crvi - tg compf_id_l //.
Qed.

Theorem c3f_fs u v:
  (nonempty (source u) \/ (nonempty (source v)) \/ (nonempty (target v))
    \/ target u = emptyset) ->
  injection u -> surjection v -> surjection (compose3function u v).
Proof. 
move=> nehyp iu sv.
have fu: function u by fct_tac. 
have fv: function v by fct_tac.  
have c3ff:= (c3f_f fu fv).
split => //; rewrite /compose3function; aw => y ys.
case: (emptyset_dichot (source u)) => nesu.
  have p:(target u = emptyset \/ nonempty (source v)).  
    case: nehyp. 
      by rewrite nesu=> [] [h] [x]; case: x.
    case; [by right | case; last by left].
    by move=> [w wt]; move: (surjective_pr sv wt)=> [x xs _];right; ex_tac.
  have: (nonempty (functions (target u) (source v))).
    by apply: (fun_set_ne p). 
  move=> [f fsp]; ex_tac; move/functionsP:(fsp) => [ff sf tf].
  rewrite c3f_V //.
  apply: (fun_set_small_source (y:=target v)); rewrite - nesu //.
  by apply: c3f_axiom.
have [s [cvs cvsi]] := (exists_right_inv_from_surj sv).
have [r [cru crui]] := (exists_left_inv_from_inj iu nesu).
have Hb: function s by fct_tac.
have Hc: function r by fct_tac.
move/functionsP:ys=> [fy sy ty].
have sf: source ((s \co y) \co r) = target u by move: cru=> [_ _]; aw.
have tf: target ((s \co y) \co r) = source v by move: cvs=> [_ _]; aw.
have sytr: source y = target r by rewrite sy; move: (f_equal target crui); aw.
have tytr: source s = target y by rewrite ty; move: (f_equal source cvsi); aw.
have csy: s \coP y by [].
have fcyr: function  (y \co r)  by fct_tac.
have csyr: s \coP (y \co r) by hnf; aw. 
have tcyr : (target (y \co r) = target v) by aw.
have fcsy: function (s \co y) by fct_tac.
have ff: function ((s \co y) \co r)  by fct_tac=>//; aw.
exists ((s \co y) \co r) ; first by apply/functionsP.
rewrite c3f_V // -(@compfA s y r) // (@compfA  v s (y \co r)) //.
rewrite cvsi -tcyr compf_id_l // -compfA // crui - sy compf_id_r //. 
Qed.

Lemma c3f_fb u v:
  bijection u -> bijection v -> bijection (compose3function u v).
Proof. 
move=> [iu su][iv sv]; split; first by apply: c3f_fi=>//. 
apply: c3f_fs=>//. 
case: (emptyset_dichot (target u)); first by right; right; right.
move=> [y yt]; move: (surjective_pr su yt)=> [x xs _]; left; ex_tac.
Qed.

Lemma Eq_pow_inv A B C D: A \Eq B -> C \Eq D ->
  functions C A \Eq functions D B.
Proof.
move=> [f [bf sf tf]] /EqS [g [bg sg tg]].
exists (compose3function g f); hnf.
rewrite {2 3} /compose3function - sf -tf - sg -tg; aw. 
by split => //;apply: c3f_fb.
Qed.

(** Isomorphism between calF(BxC,A) and calF(C, calF(B,A)) and calF(B, calF(C,A)) *)

Section PartialFunction.
Variables A B C: Set.

Let fBA := (functions B A).
Let fCA := (functions C A).
Let fBCA := (functions (B\times C) A).

Definition first_partial_fun f y:=
  Lf (fun x => Vf f (J x y))  B A.

Definition second_partial_fun f x:=
  Lf (fun y => Vf f (J x y))  C A.

Definition first_partial_function f:=
  Lf (fun y => first_partial_fun f y) C fBA.

Definition second_partial_function f:=
  Lf (fun x => second_partial_fun f x) B fCA.

Definition first_partial_map :=
  Lf (fun f=> first_partial_function f) fBCA (functions C fBA).

Definition second_partial_map :=
  Lf (fun f=> second_partial_function f) fBCA (functions B fCA).

Lemma fpf_axiom f y:
  inc f fBCA -> inc y C ->  lf_axiom (fun x => Vf f (J x y)) B A.
Proof.
by move=> /functionsP [ff sf tf] yr x xs; Wtac; rewrite sf; apply: setXp_i.
Qed.

Lemma spf_axiom f x:
  inc f fBCA -> inc x B ->  lf_axiom (fun y => Vf f (J x y)) C A.
Proof. 
by move=> /functionsP [ff sf tf] yr y xs; Wtac; rewrite sf; apply: setXp_i.
Qed.

Lemma fpf_f  f y:  inc f fBCA -> inc y C -> 
  function (first_partial_fun f y).
Proof. 
by move => pfa yr;  apply: lf_function; apply: fpf_axiom.
Qed.

Lemma spf_f f x:  inc f fBCA ->  inc x B -> 
  function (second_partial_fun f x).
Proof.
by move=> pfa yr; apply: lf_function; apply: spf_axiom.
Qed.

Lemma fpf_V f x y: inc f fBCA -> inc x B -> inc y C ->
  Vf (first_partial_fun f y) x = Vf f (J x y).
Proof. 
rewrite/first_partial_fun=> pfa xd yr.
by rewrite LfV //; apply: fpf_axiom.
Qed.
  
Lemma spf_V f x y:  inc f fBCA -> inc x B -> inc y C ->
  Vf (second_partial_fun f x) y = Vf f (J x y).
Proof.
rewrite/first_partial_fun=> pfa xd yr.
by rewrite LfV //; apply: spf_axiom.
Qed.

Lemma fpfa_axiom f: inc f fBCA ->
  lf_axiom (fun y => (first_partial_fun f y)) C fBA.
Proof. 
move=> pfa x xr; apply /functionsP; rewrite /first_partial_fun;hnf; aw.
by split => //;apply: fpf_f.
Qed.

Lemma spfa_axiom f:  inc f fBCA ->
  lf_axiom (fun x => second_partial_fun f x)B fCA.
Proof. 
move=> pfa x xr; apply /functionsP;rewrite /second_partial_fun; hnf;aw.
split => //; by apply: spf_f.
Qed.

Lemma fpfa_f f: inc f fBCA -> function (first_partial_function f).
Proof. 
by move => ax; apply: lf_function; apply: fpfa_axiom.
Qed.

Lemma spfa_f f:inc f fBCA -> function (second_partial_function f).
Proof.
by move => fpa; apply: lf_function; apply: spfa_axiom.
Qed.

Lemma fpfa_V f y: inc f fBCA -> inc y  C ->
  Vf (first_partial_function f) y = first_partial_fun f y.
Proof. 
rewrite /first_partial_function=> pfa yr.
by rewrite LfV //; apply: fpfa_axiom.
Qed.

Lemma spfa_V f x: inc f fBCA -> inc x B ->
  Vf (second_partial_function f) x = second_partial_fun f x.
Proof. 
rewrite /second_partial_function=> pfa yr.
by rewrite LfV //; apply: spfa_axiom.
Qed.


Lemma fpfb_axiom:  
  lf_axiom (fun f=> first_partial_function f) fBCA  (functions C fBA).
Proof. 
move=> x xf; apply/functionsP; rewrite / first_partial_function; split; aww.
by apply: fpfa_f.
Qed.

Lemma spfb_axiom:
  lf_axiom (fun f=> second_partial_function f) fBCA  (functions B fCA).
Proof.
move=> x xf; apply/functionsP; rewrite /second_partial_function; split; aww.
by  apply: spfa_f.
Qed.

Lemma fpfb_f: function (first_partial_map).
Proof. by apply: lf_function; apply: fpfb_axiom. Qed.

Lemma spfb_f :function (second_partial_map).
Proof. by apply: lf_function;  apply: spfb_axiom. Qed.


Lemma fpfb_V f:
  inc f fBCA -> Vf (first_partial_map) f = first_partial_function f.
Proof. 
move=> fs; rewrite  LfV //; apply: fpfb_axiom. 
Qed.

Lemma spfb_V f:
  inc f fBCA -> Vf (second_partial_map) f = second_partial_function f.
Proof. 
by move=> fs; rewrite LfV //; apply: spfb_axiom. 
Qed.

Lemma fpfb_VV f x: inc f fBCA -> inc x (B \times C) -> 
  Vf (Vf (Vf (first_partial_map) f) (Q x)) (P x) = Vf f x.
Proof.
move=> fs xp; rewrite fpfb_V=>//.
move /setX_P: xp =>[xp px qx].
by rewrite fpfa_V // fpf_V // xp.
Qed.

Lemma spfb_VV f x: inc f fBCA -> inc x (B \times C) -> 
  Vf (Vf (Vf (second_partial_map) f) (P x)) (Q x) = Vf f x.
Proof.
move=> fs xp; rewrite spfb_V=>//.
move /setX_P: xp =>[xp px qx].
by rewrite spfa_V // spf_V // xp.
Qed.


Theorem fpfa_fb:  bijection (first_partial_map).
Proof.
set f:= first_partial_map.
have sf:source f = fBCA by rewrite /f /first_partial_map; aw.
have tf: target f = functions C fBA
  by rewrite /f /first_partial_map; aw.
have ff:= fpfb_f.
split;split=>//.
  move=> x y; rewrite sf=> xs ys eq. 
  have sx: source x = B \times C by move /functionsP: xs => [_ ].
  have sy: source y = B \times C by move /functionsP: ys => [_ ].
  have ha: forall z, inc z (source x) -> Vf x z = Vf y z.
    rewrite sx  => z zp.  
    by rewrite -(fpfb_VV  xs zp) -(fpfb_VV ys zp)  eq.
  move: xs ys => /functionsP [fx _ tx] /functionsP [fy _ ty].
  by apply: function_exten=>//; try ue. 
move=> y yt.
set (g:= Lf (fun x => Vf (Vf y (Q x)) (P x))  (B \times C) A).
have ta: lf_axiom (fun x => Vf (Vf y (Q x) ) (P x))  (B \times C) A.
  move=> x /setX_P [xp pa qb].
  move: yt; rewrite tf; move /functionsP => [fy sy ty].
  have: (inc (Vf y (Q x)) (target y)) by  Wtac.
  by rewrite ty; move /functionsP=> [fW sW <-]; Wtac. 
have gsf: (inc g (source f)).
 by rewrite /g sf; apply /functionsP; hnf;aw; split => //; apply: lf_function. 
ex_tac. 
have: inc (Vf f g) (target f) by Wtac.
move:yt; rewrite tf;move=> /functionsP [fy sy ty] /functionsP [fW sW tw].
apply: function_exten => //;try ue; move => x; rewrite sy=> xs.
have: inc (Vf (Vf f g) x) (target (Vf f g)) by Wtac. 
have: inc (Vf y x) (target y) by Wtac.
rewrite tw ty; move=> /functionsP [fy1 sy1 ty1] /functionsP [fW1 sW1 tw1].
apply: function_exten=>//; try ue; rewrite sy1=> z zs. 
have psg: (inc (J z x) (source g)) by rewrite /g; aw; fprops.
rewrite/g  lf_source in psg; rewrite sf in gsf.
move: (fpfb_VV gsf psg); aw; move=> ->. 
by rewrite /g  LfV; first by aw. 
Qed.

Theorem spfa_fb: bijection (second_partial_map).
Proof.
set f:= second_partial_map.
have sf:source f = fBCA  by rewrite /f /second_partial_map; aw.
have tf: target f = functions B  fCA.
  by rewrite /f /second_partial_map; aw.
have ff: function f by apply: spfb_f.
split; split=>//.
  move=> x y; rewrite sf=> xs ys eq. 
  have sx: source x = B \times C by move /functionsP: xs => [_ ].
  have sy: source y = B \times C by move /functionsP: ys => [_ ].
  have ha: forall z, inc z (source x) -> Vf x z = Vf y z.
    rewrite sx  => z zp.  
    by rewrite -(spfb_VV xs zp) -(spfb_VV ys zp)  eq.
  move: xs ys => /functionsP [fx _ tx] /functionsP [fy _ ty].
  by apply: function_exten=>//; try ue. 
move=> y yt.
pose (g:= Lf (fun x => Vf (Vf y (P x))  (Q x))  (B \times C) A).
have ta: lf_axiom (fun x => Vf (Vf y (P x)) (Q x)) (B \times C) A.
  move=> x /setX_P [xp pa qb].
  move: yt; rewrite tf; move /functionsP => [fy sy ty].
  have : (inc (Vf y (P x)) (target y)) by Wtac.
  by rewrite ty; move /functionsP=> [fW sW <-]; Wtac. 
have gsf:  (inc g (source f)).
 by rewrite /g sf; apply /functionsP; hnf;aw; split => //; apply: lf_function. 
ex_tac. 
have: inc (Vf f g) (target f) by Wtac.
move:yt; rewrite  tf;move=> /functionsP [fy sy ty] /functionsP [fW sW tw].
apply: function_exten=>//; try ue; move => x; rewrite sy=> xs.
have: inc (Vf (Vf f g) x) (target (Vf f g)) by Wtac. 
have: inc (Vf y x) (target y) by Wtac.
rewrite tw ty; move=> /functionsP [fy1 sy1 ty1] /functionsP [fW1 sW1 tw1].
apply: function_exten=>//; try ue; rewrite sy1=> z zs. 
have psg: (inc (J x z) (source g)) by rewrite /g; aw; fprops.
rewrite/g lf_source in psg; rewrite sf in gsf.
move: (spfb_VV gsf psg); aw; move=> ->. 
by rewrite /g LfV; first by aw. 
Qed.

End PartialFunction.


Lemma Eq_powpow a b c:
  functions (b \times c) a \Eq functions c (functions b a).
Proof.
move:(@fpfa_fb a b c) => bf.
exists (first_partial_map a b c).
by split => //; rewrite /first_partial_map; aw.
Qed. 

Lemma Eq_powpow_alt a b c:
  functions (b \times c) a \Eq functions b (functions c a).
Proof.
move:(@spfa_fb a b c) => bf.
exists (second_partial_map a b c).
by split => //; rewrite /second_partial_map; aw.
Qed. 


Lemma Eq_powx1 x: (functions C1 x) \Eq x. 
Proof.
exists (Lf (fun z => Vf z C0) (functions C1 x) x).
saw;apply: lf_bijective.
- move => t /functionsP [ft st tt]; Wtac; rewrite st; apply: set1_1.
- move => u v /functionsP [fu su tu]/functionsP [fv sv tv] eq.
  by apply: (function_exten fu fv); (try ue); rewrite su => t/set1_P ->.
- move => y yx; exists (constant_function C1 x y).
       apply/functionsP; exact: (constant_prop C1 yx). 
  rewrite constant_V//; apply: set1_1.
Qed.


Definition first_projection f:= Lf (fun z=> P (Vf f z)).
Definition secnd_projection f:= Lf (fun z=> Q (Vf f z)).
Definition two_projections a b c := 
  Lf (fun z => (J (first_projection z a b)
    (secnd_projection z a c)))
  (functions a (b \times c))
  ((functions a b) \times (functions a c)).
  

Lemma two_projections_aux f a b c: function f -> source f = a ->
  target f = b \times c ->
   [/\ lf_axiom (fun z=> P (Vf f z)) a b,
     lf_axiom (fun z=> Q (Vf f z)) a c, 
    function (first_projection f a b),  
    function (secnd_projection f a c) &
    (forall x, inc x a -> Vf (first_projection f a b) x = P (Vf f x)) /\
    (forall x, inc x a -> Vf (secnd_projection f a c) x = Q (Vf f x))].
Proof. 
move=> ff sf tf. 
have ta: lf_axiom (fun z=> P (Vf f z)) a b.
  rewrite - sf ;move=> t /(Vf_target ff). 
  by rewrite tf; move => /setX_P [].
have tb: lf_axiom (fun z=> Q (Vf f z)) a c.
  rewrite - sf;move=> t /(Vf_target ff). 
  by rewrite tf ; move => /setX_P [].
rewrite /first_projection /secnd_projection. 
by split => //;try (apply: lf_function => //); split; move=>  x xa; apply:LfV.
Qed.

Lemma two_projections_ax a b c:
  lf_axiom  
    (fun z => (J (first_projection z a b)
      (secnd_projection z a c)))
    (functions a (b \times c))
    ((functions a b) \times (functions a c)).
Proof.
move=> t /functionsP [ft st tt]. 
move: (two_projections_aux  ft st tt)=> [_ _ fa fb _].
by apply: setXp_i; apply /functionsP;split => //;
   rewrite /first_projection /secnd_projection; aw. 
Qed.

Lemma two_projections_fb a b c: bijection  (two_projections a b c).
Proof.
move: (@two_projections_ax  a b c) => ta.
rewrite /two_projections; apply: lf_bijective => //.
  move=> u v /functionsP [fu su tu] /functionsP [fv sv tv] h.
  move: (pr1_def h)(pr2_def h) => sfp ssp.
  apply: function_exten=> //; try ue;rewrite su. 
  move=> x xa.
  move: (two_projections_aux fu su tu) (two_projections_aux  fv sv tv). 
  move=> [h1 h2 h3 h4 [h5 h6]][h7 h8 h9 h10 [h11 h12]]. 
  have /setX_P [<- _ _]: (inc (Vf u x)(b \times c)) by rewrite -tu; Wtac. 
  have /setX_P [<- _ _] : (inc (Vf v x)(b \times c)) by rewrite -tv; Wtac. 
  rewrite -(h5 _ xa) - (h11 _ xa) sfp -(h6 _ xa) - (h12 _ xa) ssp //.
move=> y /setX_P [yp] /functionsP [fp sp tp] /functionsP [fq sq tq].
set (f:= Lf (fun z=> J (Vf (P y) z) (Vf (Q y) z)) a (b \times c)).
have tb: (lf_axiom (fun z=> J (Vf (P y) z) (Vf (Q y) z)) a (b \times c)).
  move=> z za; apply /setXp_i; [rewrite -tp|rewrite -tq]; Wtac.
have ff:(function f) by apply: lf_function.
have sf: (source f = a) by rewrite /f; aw.  
have tf: (target f = b \times c) by rewrite /f; aw.
move: (two_projections_aux  ff sf tf) =>  [h1 h2 h3 h4 [h5 h6]].
exists f => //; first by apply /functionsP.
by rewrite - yp; congr J;
  apply: function_exten; rewrite / first_projection /secnd_projection;
  aw; trivial;
  [rewrite sp | rewrite sq ]; move=> x xsr /=; rewrite LfV //  /f LfV //; aw.
Qed.


Lemma Eq_powprod a b c:
   functions a (b \times c) \Eq functions a b \times functions a c.
Proof.
move:(two_projections_fb a b c) => h; exists (two_projections a b c).
by split => //; rewrite /two_projections; aw.
Qed. 

End Bunion.
Export Bunion.


Module Bproduct.

(** ** EII-5-3 Definition of the product of a family of sets *)

(** We have two variants of the definitions of the product; z is a functional 
graph, with the same  domain as f, and z(i) is in f(i). Note that f is not
required to be a functional graph *)

Definition productb f:=
  Zo (\Po ((domain f) \times (unionb f)))
  (fun z => [/\ fgraph z, domain z = domain f 
    & forall i, inc i (domain f) -> inc (Vg z i) (Vg f i)]).

Definition productf I f:=  productb (Lg I f).

Lemma setXb_P f x:
  inc x (productb f) <->
  [/\ fgraph x,  domain x = domain f &
    forall i, inc i (domain f) -> inc (Vg x i) (Vg f i)].
Proof. 
split; first by move/Zo_P => [] //.
move => [pa pb pc]; apply: Zo_i => //; apply/setP_P => t tx.
have gx: (sgraph x) by fprops. 
have aux: inc (P t) (domain f) by rewrite - pb; apply: domain_i1.
rewrite - (gx _ tx); apply: setXp_i => //.
by apply /setUb_P; ex_tac; rewrite (pr2_V pa tx); apply: pc.
Qed.

Lemma setXf_P I f x:
  inc x (productf I f) <->
  [/\ fgraph x, domain x = I & forall i, inc i I -> inc (Vg x i) (f i)].
Proof. 
split.
move/setXb_P; aw; move => [pa pb pc];split => //.
  by move => i iI; move: (pc _ iI); rewrite LgV.
move => [pa pb pc]; apply/setXb_P;aw;split => //.
by move => i iI; rewrite LgV //; apply: pc.
Qed.

Lemma setXb_gi X f:
  (forall i, inc i (domain X) -> inc (f i) (Vg X i)) ->
  inc (Lg (domain X) f) (productb X).
Proof.
move => H; apply/setXb_P; split; aww.
by move => i idx; rewrite LgV //; apply:H.
Qed.

  
Lemma setXb_exten f x x':
  inc x (productb f) -> inc x' (productb f) -> {inc (domain f), x =1g x'} ->
  x = x'.
Proof. 
move=> /setXb_P [fx dx px] /setXb_P [fx' dx' px'] sv.
apply: fgraph_exten=>//; ue. 
Qed.

Lemma setXf_exten I f x x':
  inc x (productf I f) -> inc x' (productf I f) -> {inc I, x =1g x'} ->
  x = x'.
Proof.
by move => pa pb pc; apply: (setXb_exten pa pb);  aw.
Qed.

(** This lemma says that we may always assume that x is a functional graph *)
Lemma productb_gr x: productb (Lg (domain x) (Vg x)) = productb x.
Proof.
set_extens t; move /setXb_P => [p1]; aw => p2 p3;apply /setXb_P; aw; 
   split => // i idg; move: (p3 _ idg); rewrite LgV //.
Qed.

Lemma unionb_gr X : unionb (Lg (domain X) (Vg  X)) = unionb X.
Proof.
set_extens t => /setUb_P; aw; move => [y ya yb]; apply/setUb_P; exists y => //.
by move: yb;rewrite LgV.
by aw.
by rewrite LgV.
Qed.

(** Projection function to component [i] *)

Definition pr_i f i:=  Lf (Vg ^~ i) (productb f) (Vg f i).

Lemma pri_axiom f i:
  inc i (domain f) ->
  lf_axiom (Vg ^~  i) (productb f) (Vg f i).
Proof. by move=> id x /setXb_P [fx dx]; apply. Qed.

Lemma pri_f f i: inc i (domain f) ->  function (pr_i f i). 
Proof. by move=> id; apply: lf_function; apply: pri_axiom. Qed.

Lemma pri_V f i x:
  inc i (domain f) -> inc x (productb f) -> 
  Vf (pr_i f i) x = Vg x i. 
Proof. by rewrite/pr_i=> id xp; rewrite LfV // ; apply: pri_axiom. Qed.

Hint Resolve pri_f : fprops.

(** Special case where the domain is empty *)

Lemma setXb_0 : productb emptyset = singleton emptyset.
Proof. 
have h:= fgraph_set0. 
apply: set1_pr.
  by apply/setXb_P;split => //; rewrite domain_set0 => i /in_set0.
by move => z /setXb_P [_]; rewrite domain_set0; move/domain_set0_P.
Qed. 

Lemma setXb_0' f:  productb (Lg emptyset f) = singleton emptyset.
Proof. rewrite /Lg funI_set0; apply: setXb_0. Qed.

(** a product is empty iff all factors are empty *)

Lemma setXb_ne f:  nonempty_fam f -> nonempty (productb f).
Proof. 
move=> hyp.
exists (Lg (domain f)(fun i=> rep (Vg f i))).
by apply:setXb_gi => i /hyp/rep_i.
Qed.

Lemma setXb_ne2 f: nonempty (productb f) -> nonempty_fam f.
Proof. 
move=> [x] /setXb_P [fg _ h i id]; move:(h _ id) => w; ex_tac. 
Qed.

(** The set of graphs is a product *)

Lemma gfunctions_P1 a b z:
  inc z (gfunctions a b) <->
  [/\ fgraph z, domain z = a & sub z (a \times b)].
Proof. 
split; first by move/Zo_P => [/setP_P pa [pb pc]].
move => [pa pb pc]; apply: Zo_i; [by apply/setP_P | done].
Qed.

Lemma gfunctions_P2 a b z:
  inc z (gfunctions a b) <->
  [/\ fgraph z, domain z = a & sub (range z) b].
Proof. 
split; first by move/gfunctions_P1 => [pa pb] /corr_propcc [_ _ pc].
move => [pa pb pc]; apply/gfunctions_P1;split => //.
apply/corr_propcc;rewrite pb;split; fprops.
Qed.

Lemma setXb_sub_gfunctions f x:
  sub (unionb f) x ->
  sub (productb f) (gfunctions (domain f) x).
Proof.
move=> su t /setXb_P [ft dt hyp]; apply/gfunctions_P2;split => //.
move=> a /(range_gP ft) [b bt]->; apply: su. 
rewrite dt in bt;union_tac.
Qed.

Lemma setXb_eq_gfunctions f x:
  (forall i, inc i (domain f) -> Vg f i = x) ->
  productb f = gfunctions (domain f) x.
Proof.
move=> prop; apply: extensionality.  
  apply: setXb_sub_gfunctions =>//.
  by move=> y /setUb_P [z zd zV]; rewrite - (prop _ zd).
move=> y /gfunctions_P2 [fy dy sr]; apply/setXb_P;split => // i id.
rewrite (prop _ id); apply: sr; rewrite - dy in id;  fprops.
Qed.

Lemma Eq_powsum a b c:
  functions (dsum b c) a \Eq functions b a \times functions c a.
Proof.
rewrite candu2_rw.
move:(Eq_pow_inv (EqR a) (Eq_indexed b C0)) => qb. 
move:(Eq_pow_inv (EqR a) (Eq_indexed c C1)) => qc.
apply: EqT (EqS (Eq_mul_inv qb qc)).
move:(disjointU2_pr b c C0_ne_C1).
set B := b *s1 C0; set C := c *s1 C1 => dbc.
apply: EqT (EqS (Eq_mul_inv (Eq_fun_set B a) (Eq_fun_set C a))).
apply: (EqT (Eq_fun_set (B \cup C) a)). apply: EqS; clear qb qc.
exists (Lf (fun z => (P z \cup Q z))
       (gfunctions B a \times gfunctions C a)(gfunctions (B \cup C) a)).
saw;apply: lf_bijective.
- move => u /setX_P[pi /gfunctions_P1 [qa qb qc] /gfunctions_P1 [qd qe qf]]. 
  apply/gfunctions_P1; split.
  + by apply: fgraph_setU2 => //; rewrite qb qe. 
  + by rewrite domain_setU2 qb qe.
  + rewrite  set2_UXl.
    move => t/setU2_P; case; [ move/ qc | move/ qf]; fprops.
- move => u v  /setX_P[pu /gfunctions_P1 [qa qb qc] /gfunctions_P1 [qd qe qf]].
  move => /setX_P[pv /gfunctions_P1 [ra rb rc] /gfunctions_P1 [rd re rf]] sv.
  apply: (pair_exten pu pv).
    set_extens t => tp.
       have /setU2_P: inc t (P v \cup Q v) by rewrite - sv; apply: setU2_1.
       case => // /rf /setX_P[_ h1 _]; move:(qc _ tp) => /setX_P[_ h2 _].
       empty_tac1 (P t).
     have /setU2_P: inc t (P u \cup Q u) by rewrite  sv; apply: setU2_1.
     case => // / qf /setX_P[_ h1 _]; move:(rc _ tp) => /setX_P[_ h2 _].
     empty_tac1 (P t).
  set_extens t => tp.
     have /setU2_P: inc t (P v \cup Q v) by rewrite - sv; apply: setU2_2.
     case => // /rc /setX_P[_ h1 _]; move:(qf _ tp) => /setX_P[_ h2 _].
     empty_tac1 (P t).
   have /setU2_P: inc t (P u \cup Q u) by rewrite  sv; apply: setU2_2.
   case => // / qc /setX_P[_ h1 _]; move:(rf _ tp) => /setX_P[_ h2 _].
   empty_tac1 (P t).
move => y  /gfunctions_P1 [qa qb] ;rewrite set2_UXl => qc.
set y1 := y \cap (B \times a); set y2 := y \cap (C \times a).
have tv: y = P (J y1 y2) \cup Q (J y1 y2).
  aw; set_extens t; last by case/setU2_P => /setI2_P [].
  move => ty; case/setU2_P:(qc _ ty) => tt.
    by apply: setU2_1;apply: setI2_i.
    by apply: setU2_2;apply: setI2_i.
exists (J y1 y2) => //; apply:setXp_i.
  apply/gfunctions_P1; split => //.
  + by apply:(sub_fgraph qa) => t /setI2_P; case.
  + set_extens t. 
      by move=> /funI_P[z /setI2_P [_ /setX_P [_  h _]] ->].
    move => tc.
    have /funI_P [s rb rc]: inc t (domain y) by rewrite qb; fprops.
    apply/funI_P; exists s => //; apply:setI2_i => //.
    case/setU2_P:(qc _ rb) => // /setX_P [_ h _].
    empty_tac1 (P s); ue.
  + by move => t /setI2_P; case.
apply/gfunctions_P1; split => //.
  + by apply:(sub_fgraph qa) => t /setI2_P; case.
  + set_extens t. 
      by move=> /funI_P[z /setI2_P [_ /setX_P [_  h _]] ->].
    move => tc.
    have /funI_P [s rb rc]: inc t (domain y) by rewrite qb; fprops.
    apply/funI_P; exists s => //; apply:setI2_i => //.
    case/setU2_P:(qc _ rb) => // /setX_P [_ h _].
    empty_tac1 (P s); ue.
  + by move => t /setI2_P; case.
Qed. 

(** Product of a single set *)

Definition product1 x a := productb (cst_graph (singleton a) x).

Lemma cst_graph_pr x y:  productb (cst_graph x y) = gfunctions x y.
Proof. 
have xd: x = domain (cst_graph x y) by aw.
by rewrite xd - setXb_eq_gfunctions - xd // => i ix; rewrite LgV.
Qed.

Lemma setX1_pr x a:  product1 x a = gfunctions (singleton a) x.
Proof. apply: cst_graph_pr. Qed.

Lemma setX1_P x a y:
  inc y (product1 x a) <-> 
    [/\ fgraph y, domain y = singleton a & inc (Vg y a) x].
Proof. 
apply: (iff_trans (setXf_P _ _ _)); split; move=> [pa pb pc];split => //.
  apply: pc; fprops.
by move => i /set1_P ->.
Qed.

Lemma setX1_pr2 f x:  domain f = singleton x ->
  product1 (Vg f x) x =  productb f.
Proof. 
move=> df.
rewrite setX1_pr -df (setXb_eq_gfunctions (x:= (Vg f x))) // df.
by move => i /set1_P ->.
Qed.

(** Canonical bijection between [x] and [product1 x a] *)

Definition product1_canon x a :=
  Lf (fun i => cst_graph (singleton a) i) x (product1 x a).

Lemma setX1_canon_axiom x a:
  lf_axiom (fun i => cst_graph (singleton a) i) x (product1 x a).
Proof. move=> y yx; apply /setX1_P;split; aww; rewrite LgV;fprops.  Qed.

Lemma setX1_canon_f x a: function (product1_canon x a).
Proof. apply: lf_function; apply: setX1_canon_axiom. Qed.

Lemma setX1_canon_V x a i:
  inc i x -> Vf (product1_canon x a) i = cst_graph (singleton a) i.
Proof.
by  move=> iw; rewrite LfV //; apply: setX1_canon_axiom. 
Qed.

Lemma setX1_canon_fb x a: bijection (product1_canon x a).
Proof. 
apply: lf_bijective.
+ by apply: setX1_canon_axiom. 
+ move=> u v ux vx /(congr1 (Vg ^~a)); rewrite !LgV; fprops.
+ move=> y /setX1_P [fy dy Vx]; ex_tac.
  rewrite -dy; apply: fgraph_exten; aww.
  by rewrite dy ;move=> z zd /=; rewrite LgV //; move /set1_P: zd => ->.
Qed.

(** A product of n sets (with n=2) is isomorphic to the product of two sets  *) 

Definition product2 x y := productf C2 (variant C0 x y).

Definition product2_canon x y :=
  Lf (fun z => (variantLc (P z) (Q z)))  (x \times y) (product2 x y).

Lemma setX2_P x y z:
  inc z (product2 x y) <-> 
  [/\ fgraph z, domain z = C2 , inc (Vg z C0) x & inc (Vg z C1) y].
Proof.
split. 
  move /(setXf_P) => [fa fb fc]; split => //.
    move: (fc _ inc_C0_C2); aww.
  move: (fc _ inc_C1_C2); aww.
move => [pa pb pc pd]; apply/(setXf_P).
by   split ; aw;trivial  => i ind; try_lvariant ind. 
Qed.

Lemma setX2_canon_axiom x y:
  lf_axiom (fun z  => variantLc (P z) (Q z))
  (x \times y) (product2 x y).
Proof. move=> t /setX_P [pt px qy]; apply/setX2_P;aw; split;fprops. Qed.

Lemma setX2_canon_f x y: function (product2_canon x y).
Proof. apply: lf_function; apply: setX2_canon_axiom. Qed.

Lemma setX2_canon_V x y z:
  inc z (x \times y) -> Vf (product2_canon x y) z =  variantLc (P z) (Q z).
Proof. move => zp;rewrite LfV //; by apply: setX2_canon_axiom. Qed.

Lemma product2_canon_fb x y:
  bijection (product2_canon x y).
Proof. 
rewrite /product2_canon.
move: (setX2_canon_axiom (x:=x) (y:=y)) => pa.
apply: lf_bijective=>//.
  move => u v /setX_P [up pux quy] /setX_P [vp pvx qvy] eq.
  move :(congr1 (Vg ^~ C0) eq) (congr1 (Vg ^~ C1) eq); aw.
  by apply: pair_exten=>//. 
move=> z /setX2_P [fz dz Va Vb].
exists (J (Vg z C0) (Vg z C1)); aww.
symmetry;apply: fgraph_exten;fprops; aw;try ue.
by move=> t td; try_lvariant td. 
Qed.

(** The product of singletons is a singleton *)

Lemma setX_set1 f: (allf f singletonp) -> singletonp (productb f).
Proof. 
move=> als; apply/singletonP; split.
  by apply: setXb_ne => i idf; move /singletonP: (als _ idf) => [].
move=> a b ap bp; apply: (setXb_exten ap bp)=> i id.
move /singletonP: (als _ id) => [ne eq]; apply: eq.
  by move/setXb_P: ap => [_ _ ]; apply.
by move/setXb_P: bp => [_ _ ]; apply.
Qed.

(** Some properties of constant graphs *)

Definition diagonal_graphp E I :=
  Zo (gfunctions I E) constantgp.

Lemma diagonal_graph_P E I x:
  inc x (diagonal_graphp E I) <->
  [/\ constantgp x, domain x = I & sub (range x) E].
Proof.
split; first by move /Zo_P => [] /gfunctions_P2 [pa pb pc] pd.
move => [pa pb pc]; apply/Zo_i => //; apply/gfunctions_P2; split => //.
by move: pa => [].
Qed.


Definition constant_functor I E:=
  Lf (fun x => cst_graph I x) E (gfunctions I E).

Lemma cf_injective I E:
  nonempty I -> injection (constant_functor I E).
Proof. 
rewrite /constant_functor;move=> [x xi]. 
apply: lf_injective.
  move=> t te; apply/gfunctions_P2. 
  split; aww.
  by move=> y /Lg_range_P [b be ->]. 
by move=> u v ue ve /(congr1 (Vg ^~ x)); rewrite !LgV.
Qed.

(**  Change of variables in a product*)

Definition product_compose f u :=
  Lf (fun x => x \cg (graph u))
  (productb f) (productf (source u) (fun k => Vg f (Vf u k))).

Section ProductCompose.
Variables (f u: Set).
Hypotheses (bu: bijection u) (tudf: target u = domain f).

Lemma pc_axiom0 c
  (g:= ((triple (domain c) (range c) c)) \co u):
  inc c (productb f)  ->
  [/\ function g, c \cg (graph u) = graph g &
    (forall i, inc i (source u) ->
    Vg (graph g) i = Vg c (Vg (graph u) i))].
Proof. 
move=> /setXb_P [fc dc eq].
have fu: function u by fct_tac. 
have cg: (c \cg (graph u) = graph g) by rewrite/g /compose; aw.
have fg: function g. 
  by rewrite/g; fct_tac; [ apply: function_pr; fprops| aw; ue]. 
split=>//.
move=> i iu; rewrite ! corresp_g.
have id: inc i (domain (c \cg graph u)).   rewrite cg /g; fprops.
  by rewrite domain_fg //; aw.
have fgc: fgraph (c \cg graph u) by ue.
have fgv: fgraph (graph u) by fprops.
move/(compg_pP):(fdomain_pr1 fgc id) => [y Jv Ju].
by move:(pr2_V fgv Jv)(pr2_V fc Ju); aw => <-.
Qed.

Lemma pc_axiom:
  lf_axiom (fun x => x \cg (graph u)) 
     (productb f) (productf (source u) (fun k => Vg f (Vf u k))).
Proof. 
move=> x xp; move: (pc_axiom0 xp) => [fg cg VV]. 
have fu: function u by fct_tac.
rewrite  cg;apply/setXb_P; split.
+ fprops.
+ by rewrite domain_fg; aw.
+ aw => i isu. rewrite LgV // (VV _ isu) -/(Vf u i).
by move /setXb_P: xp => /proj33; apply; Wtac.
Qed.

Lemma pc_f: function (product_compose f u).
Proof. by apply: lf_function; apply: pc_axiom. Qed.

Lemma pc_V x: inc x (productb f) -> 
   Vf (product_compose f u) x = x \cg (graph u).
Proof. by move => xp; rewrite LfV //; apply: pc_axiom. Qed.

Lemma pc_VV x i:
  inc x (productb f) -> inc i (source u) ->
   Vg (Vf (product_compose f u) x) i = Vg x (Vf u i).
Proof. 
move=> xp iu; rewrite pc_V //; move:(pc_axiom0 xp) => [fg -> ->] //.
Qed.

Lemma pc_fb: bijection (product_compose f u).  
Proof. 
move: (pc_f)=> fpc. 
have su: surjection u by move: bu=> [_].
have spc:  (source (product_compose f u) = productb f).
  by rewrite /product_compose; aw.
split. 
  split=>//. 
  rewrite spc=> x y xs ys eq.
  apply: (setXb_exten xs ys).
  rewrite -tudf; move=> i iu;  move: ((proj2 su) _ iu) => [z zs ->]. 
  by rewrite - (pc_VV xs zs) -(pc_VV ys zs) eq. 
split => //.
set nf:= Lg (source u) (fun k => Vg f (Vf u k)).
have tpc:target (product_compose f u) = productb nf. 
  by rewrite /product_compose; aw.
rewrite tpc spc => y yp.
set x:= Lg (domain f) (fun i => Vg y (Vf (inverse_fun u) i)).  
have xp: (inc x (productb f)).
  apply: setXb_gi => i id.
  rewrite -tudf in id; move: ((proj2 su) _ id) => [z zsu wz].
  rewrite  wz (inverse_V2 bu zsu).
  move/setXb_P: yp => [fy dy iVV].  
  by move: (iVV z); rewrite /nf; aw; rewrite LgV //; apply.
ex_tac.
have Wt: inc (Vf (product_compose f u) x) (productb nf).
  by rewrite - spc in xp; move: (Vf_target fpc  xp); rewrite tpc.
symmetry;apply: (setXb_exten Wt yp) => i; rewrite /nf; aw=> id.
have Wd: inc (Vf u i)(domain f) by rewrite -tudf; Wtac; fct_tac.
rewrite  pc_VV // (LgV Wd) (inverse_V2 bu id) //.
Qed.

End ProductCompose.

(** ** EII-5-4 Partial products *)

(** a partial product is the set of restrictions  *)

Lemma restriction_graph2 f J:
  fgraph f -> sub J (domain f) ->
  Lg J (Vg f) = f \cg (diagonal J).
Proof. 
move=> fgj sj. 
rewrite diagonal_is_identity - compg_composef.
  by rewrite/composef identity_d; apply: Lg_exten => i idx; rewrite identity_ev.
hnf;rewrite identity_r;split => //; apply: identity_fgraph.
Qed. 

(** Product of f, with indices restricted to J *)


Definition restriction_product f J := productb (restr f J).
Definition pr_j f J :=
  Lf (restr^~ J) (productb f)(restriction_product f J).

Section RestrictionProduct.
Variables (f J: Set).
Hypothesis  (jdf: sub J (domain f)).

Lemma prj_axiom:
  lf_axiom (restr^~ J) (productb f)(restriction_product f J).
Proof.
move=> x /setXb_P [fx dx iVV].
have sx: sub J (domain x) by rewrite dx.
apply/setXb_P; aw; split; fprops.
by move=> i ij; rewrite !LgV //; apply: iVV; apply: jdf.
Qed.

Lemma prj_f : function (pr_j f J).
Proof. apply: lf_function; apply: prj_axiom. Qed.

Lemma prj_V x: inc x (productb f) -> Vf (pr_j f J) x = (restr x J). 
Proof. by rewrite /pr_j =>ix;rewrite LfV //; apply: prj_axiom. Qed.

Lemma prj_VV x i:
  inc x (productb f) -> inc i J ->  Vg (Vf (pr_j f J) x) i  =  Vg x i.
Proof. 
move=> xp ij; rewrite prj_V //.
by move /setXb_P: xp => [fw dd _]; rewrite LgV //; ue. 
Qed.

End RestrictionProduct.


(** If [f] is a family of non-empty sets, any [g] defined on a subset of
 the domain of [f] with values in the partial product can be extended to the
 whole product; thus [pr_i] and [pr_j] are sujective *)

Theorem extension_psetX f J g:
  nonempty_fam f ->
  fgraph g -> domain g = J -> sub J (domain f) ->
  (forall i, inc i J -> inc (Vg g i) (Vg f i)) ->
  exists h, [/\ domain h = domain f, fgraph h,
    (forall i, inc i (domain f) -> inc (Vg h i) (Vg f i)) &
    {inc J, h =1g g} ].
Proof.
move=> alne fg dg sjdf iVV. 
set (h:= g \cup (unionf ((domain f) -s J)
  (fun i => (singleton (kpair i (rep (Vg f i))))))).
have hg: sgraph h.
  move=>t;case /setU2_P; first by move: fg=> [gg _]; apply: gg.
  move/setUf_P=> [y _ /set1_P ->]; fprops. 
have dh: domain h = domain f.
  set_extens t.
    move /(domainP hg) => [y /setU2_P []].
      move=> Jg; apply: sjdf; rewrite -dg; aw; fprops; ex_tac.
    move /setUf_P => [y' yc  /set1_P Js].
    by rewrite (pr1_def Js); move /setC_P: yc => [].
  move => tdf; apply/(domainP hg);case: (inc_or_not t J).
    by rewrite -dg; move/(domainP (proj1 fg)) => [y jg];exists y; apply:setU2_1.
  move=> ntj; exists (rep (Vg f t)).
  apply:setU2_2; apply /setUf_P; exists t;fprops.
have fgh: fgraph h. 
  split =>//. 
  move => x y; case /setU2_P => x1; case /setU2_P => y1.
  - by move: fg=> [_ ]; apply.
  - move/setUf_P: y1 => [z /setC_P  [_ nzj] /set1_P eq1] eq2.
    move: (domain_i1 x1); rewrite dg eq2 eq1; aw; contradiction.
  - move/setUf_P: x1 => [z/setC_P [_ nzj] /set1_P eq1] eq2.
    move: (domain_i1 y1); rewrite dg - eq2 eq1; aw; contradiction.
  - move/setUf_P: x1 => [x1 _ /set1_P ->]; aw.
    by move/setUf_P: y1 => [y1 _ /set1_P ->]; aw => ->.
have sV: forall i, inc i J -> Vg h i  = Vg g i.
  have sgh:  (sub g h) by move=> t; rewrite /h; aw; fprops.
  by move=> i; rewrite -dg=> ij; symmetry; apply: (sub_graph_ev fgh sgh ij). 
exists h; split => // i id.
case: (inc_or_not i J)=> hyp; first by rewrite sV //; apply: iVV.
have ic: (inc i ((domain f) -s J)) by fprops.
have Jh: (inc (kpair i (rep (Vg f i))) h).  
   by rewrite /h; apply: setU2_2; union_tac. 
by move: (pr2_V fgh Jh); aw; move=> <-; apply: rep_i; apply: alne.
Qed.

Theorem prj_fs f J:  nonempty_fam f -> sub J (domain f) -> 
  surjection (pr_j f J). 
Proof. 
move=> alne sjd;split; first by apply: prj_f. 
rewrite /pr_j=> y; aw; move/setXb_P. 
aw;move => [fy dy iVVy]. 
have iVV: (forall i, inc i J -> inc (Vg y i) (Vg f i)). 
 by move => i ij; move: (iVVy _ ij); rewrite LgV.
move: (extension_psetX alne fy dy sjd iVV) => [h [dh fgh iVVh sv]].
have hp: (inc h (productb f)) by apply/setXb_P.
ex_tac; rewrite prj_V //; rewrite -dh in sjd.
apply: fgraph_exten; aw;fprops=> x; rewrite dy => xd.
by rewrite LgV // sv.
Qed. 

Lemma pri_fs f k: nonempty_fam f ->
  inc k (domain f) -> surjection (pr_i f k). 
Proof. 
move=> alne kd.
set (J:= singleton k). 
have sjd: sub J (domain f) by move=> t; move/set1_P => ->. 
have cpc: (product1_canon (Vg f k) k) \coP (pr_i f k). 
  split; first by apply: setX1_canon_f. 
     by apply: pri_f. 
  by rewrite /product1_canon /pr_i; aw.
have fcpx:(function ((product1_canon (Vg f k) k) \co (pr_i f k))) by fct_tac. 
have prjc: (pr_j f J = (product1_canon (Vg f k) k) \co (pr_i f k)).
  apply: function_exten => //.
  - by apply: prj_f. 
  - by rewrite /pr_j/pr_i; aw. 
  - rewrite  /pr_j/pr_i/product1_canon/product1; aw.
  - rewrite/restriction_product.
    have -> //: (restr f J) = cst_graph (singleton k) (Vg f k).
    by apply: Lg_exten => t /set1_P ->.
  - move=> x xs. 
    have xp: inc x (productb f) by move: xs;rewrite /pr_j lf_source.
    have xsk: inc x (source (pr_i f k)) by rewrite /pr_i lf_source.
    have aux1: inc (Vf (pr_i f k) x) (Vg f k).
      have : (target  (pr_i f k) = Vg f k) by rewrite/pr_i; aw. 
      by move=> <-; Wtac; apply: pri_f.
    rewrite compfV // setX1_canon_V // prj_V //.
    have xp1: inc x (productb f) by [].
    move /setXb_P: xp1 => [fx dx iVVx].
    have ssk: sub (singleton k) (domain x).
       by move=> xw eq1; aw; rewrite (set1_eq eq1) dx.
    rewrite/J; apply: fgraph_exten; rewrite /cst_graph;aww.
    move=> z zk; rewrite !LgV // (set1_eq zk) pri_V //. 
apply: (left_compose_fs2 cpc).
  by rewrite - prjc; apply: prj_fs. 
move: (setX1_canon_fb (Vg f k) k)=> [ h _]; apply: h.
Qed.

(** if [X] and [Y] are functional graphs, with same domain, [productb X] is a 
subset of [productb g] if and only if the same holds for each component
(for one implication, the small product must be non-empty)
*)

Lemma setXb_monotone1 f g:
  domain f = domain g ->
  (forall i, inc i (domain f) -> sub (Vg f i) (Vg g i)) ->
  sub (productb f) (productb g).
Proof.  
move=> dfdg sVV x /setXb_P [fx dx iVV].
apply/setXb_P; rewrite -dfdg;split => // i ifg; apply: sVV; fprops. 
Qed.

Lemma setXb_monotone2 f g:
  domain f = domain g ->
  nonempty_fam f ->
  sub (productb f) (productb g)  -> 
  (forall i, inc i (domain f) -> sub (Vg f i) (Vg g i)).
Proof. 
move=> dfdg alne sfg i id j jV.
have jt: (inc j (target (pr_i f i))) by rewrite/ pr_i; aw. 
move:((proj2 (pri_fs alne id)) _  jt) => [x xs ->].
move: xs; rewrite /pr_i lf_source=>xs.
rewrite pri_V //.
by move /setXb_P: (sfg _ xs) => [fx dx]; apply; rewrite -dfdg.
Qed.


(** ** EII-5-5 associativity of products of sets *)
(** Given a product with domain I, and a partition J of I, we can consider the 
   set of mappings that associate to each j in J the partial product. 
   This is a product. Associativity says that this product of products
   is isomorphic to the initial product.
   Implies associativity of cardinal product  *)

Definition prod_assoc_axioms f g :=
  partition_w_fam g (domain f).

Definition prod_assoc_map f g :=
  Lf(fun z => (Lg (domain g) (fun l => Vf (pr_j f (Vg g l)) z)))
  (productb f) 
  (productf (domain g) (fun l => (restriction_product f (Vg g l)))).

Lemma pam_axiom f g:
  prod_assoc_axioms f g -> 
  lf_axiom(fun z => (Lg (domain g) (fun l => Vf (pr_j f (Vg g l)) z)))
  (productb f) 
  (productf (domain g) (fun l => (restriction_product f (Vg g l)))).
Proof. 
move=> [fg md u] t td; apply/setXb_P; aw; split;fprops.
move=> i id; rewrite !LgV //.
have -> : (restriction_product f (Vg g i) = target  (pr_j f (Vg g i))).
  by rewrite /pr_j; aw. 
Wtac; last by rewrite/pr_j lf_source.
apply: prj_f=> // z; rewrite -u=> tu; union_tac. 
Qed.

Lemma pam_f f g:
  prod_assoc_axioms f g -> 
  function (prod_assoc_map f g). 
Proof. by move => h; apply: lf_function; apply: pam_axiom. Qed.

Lemma pam_V f g x:
  prod_assoc_axioms f g -> inc x (productb f) ->
  Vf (prod_assoc_map f g) x = (Lg (domain g) (fun l => Vf (pr_j f (Vg g l)) x)).
Proof. by move => ax xp; rewrite LfV //; apply: pam_axiom.  Qed.

Lemma pam_fi f g:
  prod_assoc_axioms f g ->
  injection (prod_assoc_map f g).
Proof. 
move=> pa; split; first by apply: pam_f. 
have sp:(source (prod_assoc_map f g) = productb f). 
  by rewrite /prod_assoc_map; aw.
rewrite sp {sp} => x y xs ys.
rewrite (pam_V pa xs)(pam_V pa ys) => sv.
move: pa=> [fg md ugdf].
apply: (@setXb_exten _ x y xs ys) => i; rewrite - ugdf.
move/setUb_P => [z zd iV].
have svf: sub (Vg g z) (domain f) by move=> t tv; rewrite - ugdf; union_tac. 
move:(congr1 (Vg ^~ z) sv); rewrite !LgV // !prj_V // => /(congr1 (Vg ^~i)).
rewrite !LgV //.
Qed.

Theorem pam_fb f g:
  prod_assoc_axioms f g ->
  bijection (prod_assoc_map f g).
Proof. 
move=> pa; split; first by apply: pam_fi. 
split; first by apply: pam_f.
have sp: source (prod_assoc_map f g) = productb f
  by rewrite /prod_assoc_map; aw.
have tp: target (prod_assoc_map f g) =
  (productf (domain g) (fun l => restriction_product f (Vg g l))).
  by rewrite /prod_assoc_map; aw.
rewrite sp tp; move=> y yp; move /setXf_P: (yp); aw; move => [fy dy iVr].
move: (pa) => [fg md ugdf].
have sVd: forall i, inc i (domain g) -> sub (Vg g i) (domain f).
  by move=> i id v vV; rewrite -ugdf; union_tac. 
pose h i := Lf (fun z => (Vg (Vg y i) z)) (Vg g i) (unionb f).
have ta:forall i, inc i (domain g) ->
    lf_axiom (fun z => Vg (Vg y i) z) (Vg g i) (unionb f).
  move=> i id x xV; move: (sVd _ id) =>sVdi.
  apply: (@setUb_i _ x); first by apply: sVdi=>//. 
  move: (iVr  _ id); aw; move/setXb_P => [fgV deq]; aw => rel.
  by move: (rel _ xV); rewrite !LgV.
have afp: forall i, inc i (domain g) -> function_prop (h i) (Vg g i) (unionb f).
  move=> i id; rewrite /h. 
  by split; first (by  apply: lf_function; apply: ta);  aw. 
move: (extension_partition_thm pa afp) => [x [[[fx sx tx] ag] etc]].
have gxp: inc (graph x) (productb f).
  apply/setXb_P; rewrite (domain_fg fx) - sx;split; fprops.
  move=> i ix; rewrite -/(Vf x i).
  move: ix; rewrite sx -ugdf; move/(setUb_P) =>[z zdg iV].
  move: (ag _ zdg)=> [_ _ eq]; rewrite (eq _ iV) LfV //.
    move: (iVr _ zdg); aw; move/setXb_P => [qa]; aw => eq1 res.
    by move: (res _ iV); rewrite !LgV.
  by apply: (ta _ zdg).
have Wt: inc (Vf (prod_assoc_map f g)(graph x))(target (prod_assoc_map f g)).
  by Wtac; apply: pam_f.
ex_tac; apply: (setXf_exten (x:=y) (x':= Vf _ _ ) yp).
  by rewrite - tp. 
move=> i id.
have aux2: sub (Vg g i) (domain f) by apply: sVd.
have aux3: sub (Vg g i) (domain (graph x)) by rewrite domain_fg //; ue.
rewrite pam_V // LgV // prj_V //.
move: (iVr _ id); aw; move/setXb_P=> [fgy]; aw => qa qb.
apply: fgraph_exten; aw; fprops. 
move: (ag _ id)=> [aa bb cc].
move => j; rewrite qa => jd; move: (cc _ jd); rewrite LgV //.
by rewrite -/(Vf x j) => ->; rewrite LfV //;  apply: ta. 
Qed.


(** Case where the domain is partitioned in two sets *)

Lemma prod_assoc_map2 f g:
  prod_assoc_axioms f g -> domain g = C2 ->
  (productb f) \Eq
  ((restriction_product f(Vg g C0)) \times (restriction_product f (Vg g C1))).
Proof.
move=> pam dg.
set h := (productf (domain g) (fun l => (restriction_product f (Vg g l)))).
have ea: productb f \Eq h.
  exists (prod_assoc_map f g). 
  by split; first (by apply: pam_fb); rewrite /prod_assoc_map; aw.
apply: (EqT ea); apply:EqS.
exists (product2_canon (restriction_product f (Vg g C0))
    (restriction_product f (Vg g C1))). 
rewrite /bijection_prop/product2_canon; aw; split => //.
   by apply: product2_canon_fb.  
rewrite /h dg; congr (productb _); apply: Lg_exten.
move=> x xt; try_lvariant xt; fprops. 
Qed.

(** The product of two sets is equipotent to one of them if the other one 
  is a singleton. Implies that one is a unit for cardinal product.*)

Lemma first_proj_fb x y:
  singletonp y -> bijection (first_proj (x \times y)).
Proof. 
move=> sy.
set f:=first_proj (x \times y).
have gp: sgraph (x \times y) by apply: setX_graph. 
have sp: source f = (x \times y)  by rewrite /f/first_proj; aw.
have tp: target f = domain(x \times y) by rewrite /f/first_proj; aw.
have fp: function (first_proj (x \times y)) by apply: first_proj_f.
have [t ty] := sy.
split. 
  split=>//; rewrite sp=> a b ap bp.
  do 2 rewrite first_proj_V =>//. 
  move: ap bp; rewrite ty.
  move /setX_P=> [ap _] /set1_P pa /setX_P [bp _ /set1_P qb] peq. 
  apply: pair_exten=>//; ue.
split => //.
rewrite sp tp =>z /(domainP gp) [p px]; ex_tac.
by rewrite first_proj_V =>//; aw. 
Qed.

(** A product is isomorphic to a partial product if missing factors are 
  singletons. Implies that one can be removed in cardinal products. *)


Lemma prj_fb f J:
  sub J (domain f) ->
  (forall i, inc i ((domain f) -s J) -> singletonp (Vg f i)) ->
  bijection_prop (pr_j f J) (productb f) (productb (Lg J (Vg f))).
Proof. 
set (K:= ((domain f) -s J)) => sjd als.
split; [|  by rewrite/pr_j; aw | by rewrite/pr_j; aw].
have sk: sub K (domain f) by apply: sub_setC.
have sr: singletonp (restriction_product f K).
  by apply:setX_set1;fprops; hnf; aw => i ik; rewrite LgV //; apply: als.
set (g:= variantLc J K).
have paa: prod_assoc_axioms f g by apply: (is_partition_with_complement sjd).  
set (f1:= prod_assoc_map f g). 
have bf1: bijection f1 by apply: pam_fb. 
have ff1:function f1 by fct_tac.
set (xa:= restriction_product f (Vg g C0)).
set (xb:= restriction_product f (Vg g C1)).
set (f2:= inverse_fun (product2_canon xa xb)).
have dg: domain g = C2 by rewrite /g; aw.
have Va: Vg g C0 = J by rewrite /g; aw. 
have Vb: Vg g C1 = K by rewrite /g; aw. 
have bf2: bijection f2  by apply: inverse_bij_fb; apply: product2_canon_fb.
have ff2: function f2 by fct_tac.
have sf2tf1: source f2 = target f1.
  rewrite lf_target ifun_s lf_target dg; congr (productb _).
  by apply: Lg_exten=>//; move=> v vt; try_lvariant vt. 
set (f3:= first_proj (xa \times xb)).
have sb: singletonp xb. 
  by rewrite /xb /restriction_product Vb; apply: sr.
have bf3: bijection f3 by apply: first_proj_fb. 
have sf3tf2: source f3 = target f2 by rewrite ifun_t ! lf_source.
have cf3f3: f3 \coP f2 by rewrite /f3/f2; split=>//; fct_tac. 
have bcf3f2: bijection (f3 \co f2) by apply: compose_fb.
have cf3f2f1: (f3 \co f2) \coP f1 by split; aw=>//; fct_tac.  
suff: (pr_j f J =  (f3 \co f2) \co f1) by move=> ->; apply: compose_fb.
have sp: source (pr_j f J) = source f1 by rewrite !lf_source.
have nexb: nonempty xb by move/singletonP: sb => [].
apply: function_exten; aw; trivial.
      by apply: prj_f=>//. 
    by fct_tac.
  by rewrite !lf_target  setX_domain // /xa Va.
rewrite sp=> x xs.
move xW: (Vf f1 x) =>y.
move yW: (Vf f2 y)=>z.
have yt: inc y (source f2) by rewrite -xW sf2tf1 ; fprops.
have zt: inc z (target f2) by rewrite -yW; Wtac.
have Jg2: (inc (kpair y z) (graph f2)) by rewrite -yW; Wtac.
have fp: function (product2_canon xa xb) by apply: setX2_canon_f.
have zs: inc z (source (product2_canon xa xb)) by move: zt; rewrite ifun_t.
have zp: inc z (xa \times xb) by move: zs; rewrite lf_source.
rewrite compfV // compfV //; last by rewrite xW.
rewrite xW yW first_proj_V //.
move: Jg2; rewrite /f2; aw; move/igraph_pP => Jg3.
move: (Vf_pr2 fp Jg3); aw; rewrite setX2_canon_V =>//.
move /(congr1 (Vg ^~C0)); aw => <-.
move: xs; rewrite lf_source => xdd.
have  zd: inc C0 (domain g) by  rewrite dg; fprops.
by rewrite -xW /f1 pam_V // LgV // Va.
Qed.

(** ** EII-5-6 distributivity formulae *)
(** Given a double family Xij, union over I of intersection over J is 
intersection of union, and  conversely. The new index set is a product. *)

Theorem distrib_union_inter f:
  (forall l, inc l (domain f) -> nonempty (domain (Vg f l))) ->
  unionf (domain f) (fun l => intersectionb (Vg f l)) =
  intersectionf (productf (domain f) (fun l => (domain (Vg f l))))
  (fun g => (unionf (domain f) (fun l => Vg (Vg f l) (Vg g l)))).
Proof.
move=> alne; set_extens s => xu.
  apply: setIf_i.
    by apply: setXb_ne; fprops; hnf; aw => i id; rewrite LgV //; apply: alne.
  move /setUf_P: xu => [y yf si] j /setXf_P [fgj dj]; aw => aa.
  move: (aa _ yf); aw => bb; move: (setIb_hi si bb) => cc; union_tac. 
ex_middle nsu.
set gl:= (fun l => Zo (domain (Vg f l)) (fun i =>  ~ (inc s (Vg (Vg f l) i)))).
have ne: (nonempty  (productf (domain f) gl)).
  apply: setXb_ne; fprops; hnf; aw=> i id; rewrite LgV // /gl; set jl:=Zo _ _ . 
  case: (emptyset_dichot jl) =>// je; case: nsu; union_tac.
  apply: setIb_i; [by apply /domain_set0P; apply: alne | ].
  by move=> j jd; ex_middle hyp; empty_tac1 j; apply: Zo_i.
move: ne=> [y] /setXf_P [fy dy iVz].
have yp: inc y (productf (domain f) (fun l => domain (Vg f l))). 
  apply/setXf_P; split =>// i id.
  by case /Zo_P: (iVz _ id).  
by move /setUf_P: (setIf_hi xu yp) => [z zdf sv]; case/Zo_P: (iVz _ zdf).
Qed.

Theorem distrib_inter_union f: (* needs AC *)
  intersectionf (domain f) (fun l => unionb (Vg f l)) =
  unionf (productf (domain f) (fun l => (domain (Vg f l))))
  (fun g => (intersectionf (domain f) (fun l => Vg (Vg f l) (Vg g l)))).
Proof.
set_extens x => xi; last first.
  move /setUf_P: xi  => [y /setXf_P [_ dy Vd] xi1].
  case: (emptyset_dichot (domain f)) => ne.
  by move: xi1; rewrite ne setIf_0 => /in_set0.
  apply: (setIf_i ne) => j jd; move: (setIf_hi xi1 jd)=> u; union_tac.
pose prop j a := (inc a (domain (Vg f j)) /\  inc x (Vg (Vg f j) a)).
pose yf j:= choose (prop j).
have p1: (forall j, inc j (domain f) -> (prop j (yf j))).
  move=> j jd; apply: choose_pr; move /setUb_P:(setIf_hi xi jd).
  by move => [y y1 y2];exists y; split.
apply: (@setUf_i _ (Lg (domain f) yf)).  
  by apply/setXf_P; split;aww=> i id; rewrite LgV//; move: (p1 _ id)=>[].
case: (emptyset_dichot (domain f)) => ne.
  by move: xi; rewrite ne setIf_0 => /in_set0.
by apply: (setIf_i ne) => j jd; rewrite LgV //; move: (p1 _ jd) => [].
Qed.

(** Variants of distributivity of union and intersection of Xij
 when one index set has two elements *)


Lemma distrib_union2_inter f g:
  nonempty (domain f) -> nonempty (domain g) ->
  (intersectionb f) \cup (intersectionb g) =
  intersectionf((domain f) \times (domain g)) 
     (fun z => ((Vg f (P z)) \cup (Vg g (Q z)))).
Proof. 
move => nef neg.
have nep:nonempty ((domain f) \times (domain g)). 
  by move: nef neg=> [x xd][y yd]; exists (J x y); fprops.
set_extens x => xu.
  apply: (setIf_i nep)=> j /setX_P [pj p1 p2]; case /setU2_P: xu=>p.
    by move: (setIb_hi p p1)=>a; fprops.
  by move: (setIb_hi p p2)=>a; fprops.
case: (inc_or_not x (intersectionb f))=> p; [fprops | apply: setU2_2].
move: nef neg; move/domain_set0P => nef1 /domain_set0P neg1.
have [z1 z1d nexv]: (exists2 z1, inc z1 (domain f) & ~ (inc x (Vg f z1))). 
  ex_middle bad;case: p. 
  apply: (setIb_i nef1) => i id; ex_middle xx; case: bad; ex_tac.
apply: (setIb_i neg1) => i id; move /(setIf_P _ nep): xu => h.
by move: (h _ (setXp_i z1d id)); aw; case/setU2_P.
Qed.

Lemma distrib_inter2_union f g:
  (unionb f) \cap (unionb g) =
  unionf((domain f) \times (domain g)) 
   (fun z => ((Vg f (P z)) \cap (Vg g (Q z)))).
Proof. 
set_extens x.
  move /setI2_P => [] /setUb_P [y yd xf] /setUb_P [z zd xg].
  apply/setUf_P; exists (J y z);aw; fprops.
move /setUf_P=> [y /setX_P [yp yf yg] /setI2_P [pa pb]].
apply/setI2_P; split; union_tac.
Qed.

(** Distributivity of product over union and intersection *)

Theorem distrib_prod_union f:
  productf (domain f) (fun l => unionb (Vg f l)) =
  unionf (productf (domain f) (fun l => (domain (Vg f l))))
  (fun g => (productf (domain f) (fun l => Vg (Vg f l) (Vg g l)))).
Proof.
case: (emptyset_dichot (domain f)) => p. 
  by rewrite p /productf /Lg !funI_set0 !setXb_0 setUf_1 funI_set0 setXb_0.
case: (p_or_not_p (forall l, inc l (domain f) -> nonempty (domain (Vg f l)))).
  move=> alned.
  set_extens x => xp; last first.
    move: xp => /setUf_P [y /setXf_P [fy dy py] /setXf_P [fx dx px]].
    by apply/setXf_P;split => // i idf; apply: (@setUb_i _ (Vg y i)); fprops. 
  move: xp=> /setXf_P [gx dx px].
  have : (nonempty (productf (domain f) (fun l =>
    (Zo (domain (Vg f l)) (fun i => (inc (Vg x l) (Vg (Vg f l) i))))))).
    apply: setXb_ne; fprops; hnf;hnf; aw;move=> i id; rewrite LgV//.
    by move /setUb_P: (px _ id) => [y yd iVV]; exists y; apply: Zo_i.
  move=> [y /setXf_P [fy dy py] ].
  by apply: (@setUf_i _ y); apply/setXf_P;
      split => // i idf;case /Zo_P: (py _ idf).
move=> special.
have [x xd de]: exists2 l, inc l (domain f) & domain (Vg f l) = emptyset.
  ex_middle aux; case: special=> l ld.
  case: (emptyset_dichot (domain (Vg f l)))=>// pp. 
  case: aux; ex_tac.
have ->: productf (domain f) (fun l => domain (Vg f l)) = emptyset.
  apply /set0_P => t/setXf_P [pa pb pc].
  by move: (pc _ xd); rewrite de => /in_set0.
rewrite setUf_0;apply /set0_P => t /setXf_P [pa pb pc].
by move: (pc _ xd); move/domain_set0_P: de => ->;rewrite setUb_0 => /in_set0.
Qed.

Theorem distrib_prod_intersection f:
  (forall l, inc l (domain f) -> nonempty (domain (Vg f l))) ->
  productf (domain f) (fun l => intersectionb (Vg f l)) =
  intersectionf (productf (domain f) (fun l => (domain (Vg f l))))
  (fun g => (productf (domain f) (fun l => Vg (Vg f l) (Vg g l)))).
Proof.
move=> alne.
have nep:(nonempty (productb (Lg (domain f) (fun l => domain (Vg f l))))).
  by apply: setXb_ne; fprops;hnf; hnf; aw => i id;rewrite LgV//; apply: alne.
set_extens x => xp. 
  apply: (setIf_i nep) =>j /setXf_P [fj dj iVd].
  move /setXf_P: xp=>[fx xd iVi];apply/setXf_P; split => // i id. 
  move: (iVi _ id) => ivdi; apply: (setIb_hi ivdi (iVd _ id)). 
move: nep=> [u up]; move: (setIf_hi xp up) => /setXf_P [fx dx iVx].
apply/setXf_P; split => // i id; apply: setIb_i; [ | move=> j jd].
  by apply/domain_set0P; apply: alne.
have: (nonempty (productf (domain f) (fun l =>
    (Zo (domain (Vg f l)) (fun jj => l = i  -> jj = j))))).
  apply: setXb_ne; fprops; hnf; hnf;aw=> k kd; rewrite LgV //.
  case: (equal_or_not k i)=> ki; first by exists j; apply: Zo_i; ue.
  move: (alne _ kd) => [y yd]; exists  y; apply: Zo_i=>//. 
move=> [y] /setXf_P [fy dy iV]; move: (iV _ id); move/Zo_P => [_ aux].
have yd: (inc y (productf (domain f) (fun l => domain (Vg f l)))).
  by apply /setXf_P; split => // k kdf; move /Zo_P: (iV _ kdf) =>[].
move/setXf_P: (setIf_hi xp yd) =>[_ _ rel].
by move: (rel _ id); rewrite aux.
Qed.



(** A partition on each [X_i] induces a partition on the product *)

Lemma partition_product f:
  (forall l, inc l (domain f) -> (partition_w_fam (Vg f l) (unionb (Vg f l)))) 
   -> partition_w_fam(Lg(productf (domain f) (fun l => domain (Vg f l)) ) 
    (fun g => (productf (domain f) (fun l => Vg (Vg f l) (Vg g l)))))
  ( productf (domain f) (fun l => unionb (Vg f l))).
Proof. 
move=> alp;split; first by fprops.
  move=> i j; rewrite Lgd => ip jp; rewrite ! LgV //.
  alt_tac ij.
  hnf; set int:=  _ \cap  _.
  case: (emptyset_dichot int) =>// ei.
  case: ij; move: ei=> [xi]; rewrite/int; aw.
  move: ip jp => /setXf_P [fi di vi] /setXf_P  [fj dj vj]
     /setI2_P [] /setXf_P [fx dx eq1] /setXf_P  [_ _ eq2]. 
  apply: fgraph_exten =>//; try ue. 
  move=> x; rewrite di =>  xd; move: (eq1 _ xd) (eq2 _ xd) (alp _ xd).
  rewrite /partition_w_fam; move=> eq3 eq4 [fgV md _].
  move: (vi _ xd) (vj _ xd)=>  eq5 eq6; case: (md _ _ eq5 eq6) =>// dij.
  empty_tac1 (Vg xi x). 
rewrite distrib_prod_union /unionb;aw;apply: setUf_exten =>// i ip.
by rewrite LgV.
Qed.

(** Special cases when one index set has only two elements *)

Lemma distrib_prod2_union f g:
  product2 (unionb f)(unionb g) =
  unionf((domain f)\times  (domain g))
      (fun z => (product2 (Vg f (P z)) (Vg g (Q z)))).
Proof. 
rewrite /product2; set_extens x. 
  move /setXf_P => [fx dx iV].
  have Tat: inc C0 C2 by fprops.  
  have Tbt: inc C1 C2 by fprops. 
  move: (iV _ Tat) (iV _ Tbt); aw. 
  move=> /setUb_P [u ud uVV] /setUb_P [v vd vVV]; apply/setUf_P.
  exists (J u v);  fprops; apply/setXf_P;split => //.
  by move=> i ind;  try_lvariant ind; aw.
move/setUf_P=>[y] /setX_P [yp py qy] /setXf_P [fx dx iV]; apply/setXf_P.
split => // i idx; move: (iV _  idx); try_lvariant idx; move=> ?; union_tac.
Qed.

Lemma distrib_prod2_inter f g:
  product2 (intersectionb f)(intersectionb g)=
  intersectionf((domain f)\times (domain g)) (fun z => 
    (product2 (Vg f (P z)) (Vg g (Q z)))).
Proof.
rewrite/product2; set_extens x.
  move /setXf_P=> [fx dx iVv].
  case: (emptyset_dichot (domain f \times domain g)) => xx.
    move: (iVv _ inc_C0_C2) (iVv _ inc_C1_C2); aw; rewrite /intersectionb.
    case: (setX_0 xx) => ->; rewrite setIf_0. 
       by move => /in_set0.
       by move => _ /in_set0.
  apply :(setIf_i  xx) => j. 
  move/setX_P => [jp pj qj]; apply/setXf_P;split => // i id. 
  move: (iVv _ id); try_lvariant id => Vi; first by apply: (setIf_hi Vi pj).
  by apply:  (setIf_hi Vi qj).
case: (emptyset_dichot (domain f \times domain g)) => xx.
  by rewrite xx setIf_0 => /in_set0. 
move/(setIf_P _ xx) => h.
move: xx => [j jp]; move: (h _ jp) => /setXf_P [pa pb pc].
move /setX_P: jp => [_ ja jb].
have nef: nonempty f by apply /domain_set0P; ex_tac.
have neg: nonempty g by apply /domain_set0P; ex_tac.
have aux:  (forall i j, inc i (domain f) -> inc j (domain g) -> 
    (inc (Vg x C0) (Vg f i) /\ inc (Vg x C1) (Vg g j))).
  move=> i k id kd.
  have Jd: (inc (J i k) ((domain f) \times  (domain g))) by fprops.
  move: (h _ Jd) => /setXf_P [fx dx px].
  by move: (px _ inc_C0_C2)(px _ inc_C1_C2); aw; aw => qa qb; split.
apply/setXf_P;split => // i itp; try_lvariant itp; apply setIb_i => // k kd.
  by move: (aux _ _ kd jb) => [].
by move: (aux _ _ ja kd) => [].
Qed.

Lemma distrib_product2_union f g:
  (unionb f) \times (unionb g) =
  unionf((domain f) \times  (domain g)) (fun z => 
    ((Vg f (P z)) \times  (Vg g (Q z)))).
Proof. 
move: (distrib_prod2_union f g); rewrite/product2 => distr.
set_extens x. 
  move /setX_P=> [xp px qx].
  set (v := variantLc (P x) (Q x)).
  have: inc v (productb (variantLc (unionb f) (unionb g))).
    by apply/setXb_P;rewrite/v; aw; split; fprops => i it; try_lvariant it. 
  rewrite /productf in distr;  rewrite variantLc_prop distr.
  move /setUf_P => [y p1 p2]; apply/setUf_P; ex_tac.
  move /setXf_P: p2=> [fv]; aw => dv p; apply/setX_P.
  move: (p _ inc_C0_C2) (p _ inc_C1_C2); rewrite /v; aw; split;fprops.
move /setUf_P=> [y yp /setX_P [px xp xq]].
set (qx := variantLc (P x) (Q x)).
have:(inc qx (productb (variantLc  (unionb f) (unionb g)))). 
  move: distr; rewrite/productf -variantLc_prop; move=>->.
  union_tac; apply/setXf_P;rewrite /qx; aw;split; fprops.
  move=> i it; try_lvariant it; fprops.
move/setXf_P=> [fq dx vqx]; apply/setX_P.
by move: (vqx _ inc_C0_C2) (vqx _ inc_C1_C2); rewrite /qx;aw. 
Qed.

Lemma distrib_product2_inter f g:
  (intersectionb f) \times  (intersectionb g) =
  intersectionf((domain f) \times (domain g)) (fun z => 
    ((Vg f (P z)) \times  (Vg g (Q z)))).
Proof. 
move: (distrib_prod2_inter f g); rewrite / product2=> distr.
set_extens x => xp.
  set (qx :=  variantLc (P x) (Q x)).
  have: inc qx (productb (variantLc (intersectionb f) (intersectionb g))).
    move /setX_P: xp =>[xp pxf qxg]; apply/setXf_P. 
    rewrite /qx /C2; aw;split; fprops.
    by move=> i ind; try_lvariant ind.
  move: distr; rewrite /productf -variantLc_prop; move=> -> qxp.
  case: (emptyset_dichot (domain f \times domain g)) => xx.
    by move: qxp; rewrite xx setIf_0 => /in_set0.
  apply /(setIf_P _ xx)=> j jp;move /setXf_P : (setIf_hi qxp jp)=> [fgq dq vq].
  move /setX_P : xp => [pa pb pc]; apply/setX_P. 
  move: (vq _ inc_C0_C2)(vq _ inc_C1_C2); rewrite /qx;aw;split;fprops.
set (qx :=  variantLc (P x) (Q x)).
case: (emptyset_dichot (domain f \times domain g)) => xx.
  by move: xp; rewrite xx setIf_0 => /in_set0.
have: inc qx (productb (variantLc (intersectionb f) (intersectionb g))).
  move: distr; rewrite /productf variantLc_prop; move =>->. 
  apply (setIf_i xx)=> j jp; move /setX_P: (setIf_hi xp jp) =>  [_ Px Qx].
  apply/setXf_P; rewrite /qx;split; aww.
  move=> i it;  try_lvariant it; fprops.  
move/setXf_P => [_ _]; rewrite /qx; aw => qv.
move: xx=> [w wp]; move /setX_P: (setIf_hi xp wp) =>  [px _ _]; apply /setX_P.
by move: (qv _ inc_C0_C2) (qv _ inc_C1_C2); aw. 
Qed.

(** A variant of distributivity, valid if the domain of the double family 
is a rectangle; works only for intersection.  *)

Theorem distrib_inter_prod f sa sb:
  (nonempty sa \/ nonempty sb) ->
  intersectionf sb (fun k => productf sa (fun i=> Vg f (J i k))) =
  productf sa (fun i => intersectionf sb (fun k=> Vg f (J i k))).
Proof.
move=> aux ; set_extens x => xi.
  case: (emptyset_dichot sb) => nb.
    by move: xi; rewrite nb setIf_0 => /in_set0.
  move: (nb)=> [y yb]; move /setXf_P: (setIf_hi xi yb) => [fx dx px]. 
  apply /setXf_P;split=> // i id; apply: (setIf_i nb).
  by move => j jsb; move: (setIf_hi xi jsb) => /setXf_P [_ _]; apply.
move /setXf_P: xi => [fx dx px].
case: (emptyset_dichot sb) => nsb.
  case: aux; last by rewrite nsb; case /nonemptyP.
  by move => [t ta]; move: (px _ ta); rewrite nsb setIf_0 => /in_set0.
apply: (setIf_i nsb) => j jsb; apply/ setXf_P;split => // i id.
move: (px _ id)=> xi; apply: (setIf_hi xi jsb).
Qed.

Lemma distrib_prod_inter2_prod f g:
  fgraph f -> fgraph g -> domain f = domain g -> 
  (productb f) \cap (productb g) =
  productf (domain f) (fun i => (Vg f i) \cap (Vg g i)).
Proof. 
move=> ff fg dfdg; set_extens x.
  move=> /setI2_P [] /setXb_P [fx dx vx] /setXb_P [ _ dx' vx'].
  apply /setXf_P;split => // i id.  
  by apply: setI2_i; [apply: vx | apply: vx'; ue]. 
move /setXf_P=> [fx dx vx]; apply: setI2_i. 
  by apply /setXb_P;split => // i idf; case /setI2_P: (vx _ idf).
by apply /setXb_P; rewrite - dfdg; split => // i idf; case /setI2_P: (vx _ idf).
Qed.

Lemma distrib_inter_prod_inter f g:
    domain f = domain g -> 
    product2 (intersectionb f) (intersectionb g) =
    intersectionf (domain f) (fun i => product2 (Vg f i) (Vg g i)).
Proof.
move=> dfdg; set (sb:= domain f).  
pose (h:= Lg (product C2 sb) (fun i => Yo (P i = C0) (Vg f(Q i)) (Vg g (Q i)))).
move: C0_ne_C1 => ns.
have <-: intersectionf sb(fun k  => productf C2 (fun i => Vg h (J i k)))
    = intersectionf sb  (fun i  =>  product2 (Vg f i) (Vg g i)).
  apply: setIf_exten. 
  move=> i isb /=; congr (productb _ );apply: Lg_exten=> x xp.
  rewrite /h; try_lvariant xp; rewrite LgV //; aw;
     try Ytac0 =>//; apply:setXp_i; fprops.
have aux: nonempty C2 \/ nonempty sb  by left; exists C0; fprops.
rewrite (distrib_inter_prod h aux); congr (productb _);apply: Lg_exten=> x xp.
try_lvariant xp; [ | rewrite  /intersectionb - dfdg]; apply: setIf_exten;
  move => i id; rewrite LgV // ; aw; (try Ytac0 => //); apply:setXp_i; fprops.
Qed.


Lemma distrib_prod2_sum A f:
  A \times (unionb f) = unionb (Lg (domain f) (fun x => A \times (Vg f x))).
Proof. 
set_extens t.
  move=> /setX_P [pt ptA] /setUb_P [y ydf Qv]; apply/setUb_P; aw; ex_tac.
  by rewrite LgV //; apply :setX_i.
move/setUb_P; aw; move=> [y ydf]; rewrite LgV //; move=> /setX_P [pr PA QV].
by apply/setX_P; split => //;apply /setUb_P;exists y.
Qed.

(** Product of two products of family of sets *)

Definition prod_of_fgraph x x':=
  Lg (domain x)(fun i => J (Vg x i) (Vg x' i)).

Definition prod_of_products_canon f f':=
  Lf (fun w => prod_of_fgraph (P w) (Q w))
  ((productb f) \times (productb f'))
  (productf (domain f)(fun i => (Vg f i) \times  (Vg f' i))).

Definition prod_of_product_aux f f' :=
  fun i =>  ((Vf f i) \times (Vf f' i)).

Definition prod_of_prod_target f f' :=
  fun_image(source f)(prod_of_product_aux f f').

Definition prod_of_products f f' :=
  Lf (prod_of_product_aux f f')(source f)(prod_of_prod_target f f').

Lemma prod_of_products_f f f':
  function (prod_of_products f f').
Proof. apply:lf_function => x xs; apply /funI_P; ex_tac. Qed.

Lemma prod_of_products_V f f' i:
  inc i (source f) ->
  Vf (prod_of_products f f') i =  (Vf f i) \times (Vf f' i).
Proof. 
move=> isf;rewrite LfV // => x xs; apply /funI_P; ex_tac.
Qed.


Section ProdProdCanon.
Variables (f f': Set).
Hypotheses (ff:function f) (ff': function f').
Hypothesis (sfsf:source f = source f').

Lemma prod_of_function_axioms x x':
  inc (graph x) (productb (graph f)) -> inc (graph x') (productb (graph f')) ->
  lf_axiom (fun i => J (Vf x i) (Vf x' i)) 
     (source f) (union (prod_of_prod_target f f')).
Proof. 
move=> gp gp' y ys.
apply: (@setU_i _ ((Vf f y) \times  (Vf f' y)));
  last by apply/funI_P; ex_tac.
apply/setXp_i.
  move /setXb_P: gp=> [fgx dgx p1]; apply:p1; rewrite domain_fg //.
move /setXb_P: gp'=> [fgx dgx p1]; apply:p1; rewrite domain_fg //; ue.
Qed.

Lemma prod_of_function_V x x' i:
  inc x (productb (graph f)) ->  inc x' (productb (graph f')) ->
  inc i (source f) -> 
  Vg (prod_of_fgraph x x') i =  J (Vg x i) (Vg x' i).
Proof. 
rewrite /prod_of_fgraph=>  xp x'p isf; rewrite LgV //.
by move/setXb_P: xp=> [_ -> _];rewrite domain_fg.
Qed.

Lemma prod_of_function_f x x':
  inc x (productb (graph f)) ->  inc x' (productb (graph f')) ->
  inc (prod_of_fgraph x x')
  (productb (graph (prod_of_products f f'))).
Proof. 
move=>  xp x'p. 
move: (prod_of_products_f f f') => fp.
move:(domain_fg ff) => eq1.
move/setXb_P: (xp)=>  [fgd  dx]; rewrite eq1 => ivv.
move/setXb_P: x'p=>  [fgd' dx'] => ivv'.
apply/setXb_P; rewrite  (domain_fg fp) lf_source.
rewrite /prod_of_fgraph; split; [ fprops | aw; ue | ].
move=> i idx; rewrite LgV //; last by rewrite dx eq1.
rewrite -/(Vf _ _) (prod_of_products_V _ idx).
apply:setXp_i; first by apply: (ivv i idx).
by apply: ivv'; rewrite (domain_fg ff') - sfsf.
Qed.

Lemma popc_target_aux:
  productb(Lg (domain (graph f))
    (fun i => (Vg (graph f) i) \times  (Vg (graph f') i))) =
  productb (graph (prod_of_products f f')).
Proof. 
congr (productb _).
move: (prod_of_products_f f f') => fp.
apply: fgraph_exten; fprops; aw; rewrite !domain_fg //.
   by rewrite lf_source.
move=> x xd; rewrite LgV //.
symmetry; exact: (prod_of_products_V f' xd).
Qed.

Lemma popc_axioms:
  lf_axiom(fun w => prod_of_fgraph (P w) (Q w))
  ((productb (graph f)) \times (productb (graph f')))
  (productb (graph (prod_of_products f f'))).
Proof. 
move=> x xd /=.
by move/setX_P: xd => [pxd px qx]; apply: prod_of_function_f.
Qed.

Lemma popc_V  w:
  inc w ((productb (graph f)) \times  (productb (graph f'))) ->
  Vf (prod_of_products_canon (graph f) (graph f')) w = 
  prod_of_fgraph (P w) (Q w).
Proof.
by move=> h; rewrite LfV // /productf popc_target_aux; apply: popc_axioms.
Qed.

Lemma popc_fb:
  bijection (prod_of_products_canon (graph f) (graph f')).
Proof. 
move: (domain_fg ff) (domain_fg ff') => fa f'a.
apply: lf_bijective.
- by rewrite/productf popc_target_aux //; apply: popc_axioms.
- move => x y xs ys sv.
  move: (xs)(ys) => /setX_P [xp px qx] /setX_P [yp py qy].
  have sj: forall i, inc i (source f) ->
    J (Vg (P x) i) (Vg (Q x) i) = J (Vg (P y) i) (Vg (Q y) i).
    move => j js. 
    by rewrite -(prod_of_function_V px qx js) -(prod_of_function_V py qy js) sv.
  apply: pair_exten => //. 
    apply: (setXb_exten px py).
    move => i; rewrite fa => js;  exact: (pr1_def (sj _ js)).
  apply: (setXb_exten qx qy).
  move => i; rewrite f'a - sfsf => js;exact: (pr2_def (sj _ js)).
- rewrite /productf popc_target_aux => y. 
move: (prod_of_products_f f f') => fc.
move /setXb_P=> [fy]; rewrite domain_fg //; rewrite lf_source => pa pb.
set xa:= Lf (fun i => P (Vg y i)) (source f)(union (target f)).
set xb:= Lf (fun i => Q (Vg y i)) (source f)(union (target f')).
have ta: lf_axiom (fun i  => P (Vg y i)) (source f) (union (target f)).
  move=> t tf /=; move:(pb _ tf); rewrite -/(Vf _ _) (prod_of_products_V f' tf).
  move/setX_P =>  [_ iP _]; apply: (@setU_i _ (Vf f t)) => //; Wtac.
have tb: lf_axiom (fun i  => Q (Vg y i)) (source f) (union (target f')).
  move=> t tf /=; move:(pb _ tf); rewrite -/(Vf _ _) (prod_of_products_V f' tf).
  move/setX_P =>  [_ _ iQ]; apply: (@setU_i _ (Vf f' t)) => //; Wtac. 
have fxa: function xa by apply: lf_function. 
have fxb: function xb by apply: lf_function. 
have sxa: source xa = source f  by rewrite /xa; aw.
have sxb: source xb = source f  by rewrite /xb; aw.
have ixa :inc (graph xa) (productb (graph f)).
  apply /setXb_P;rewrite fa (domain_fg fxa);split; fprops.
  move => i isf; rewrite /xa -/(Vf _ _) (LfV ta isf).
  move: (pb _ isf); rewrite -/(Vf _ _) (prod_of_products_V f' isf). 
  by move/setX_P => [_ ].
have ixb :inc (graph xb) (productb (graph f')).
  apply /setXb_P;rewrite f'a (domain_fg fxb);split; fprops.
    by rewrite sxb - sxa - sfsf.
  rewrite - sfsf; move => i isf; rewrite /xb -/(Vf _ _) (LfV tb isf).
  move: (pb _ isf); rewrite -/(Vf _ _) (prod_of_products_V f' isf). 
  by move/setX_P => [_ ].
exists (J (graph xa) (graph xb));fprops; aw.
rewrite /prod_of_fgraph (domain_fg fxa) lf_source.
symmetry;apply: fgraph_exten;fprops; aw; first by ue.
move => i isf; rewrite LgV //.
rewrite /xa -/(Vf _ _) (LfV ta isf) /xa -/(Vf _ _) (LfV tb isf).
move: (pb _ isf); rewrite -/(Vf _ _) (prod_of_products_V f' isf). 
by move/setX_P => [-> _].
Qed. 

End ProdProdCanon.

(** ** EII-5-7 Extensions of mappings to products *)

Definition ext_map_prod_aux x  f := fun i=> Vg  (f i) (Vg x i).
Definition ext_map_prod I src trg f :=
  Lf (fun x => Lg I (ext_map_prod_aux x f))
    (productf I src ) (productf I trg).

Definition ext_map_prod_axioms I src trg f :=
  forall i, inc i I -> 
     [/\ fgraph (f i), domain (f i) = src i & sub (range (f i)) (trg i)].

Section ExtMapProd.
Variables (I: Set) (src trg f: Set-> Set).
Hypothesis ax:  ext_map_prod_axioms I src trg f.

Lemma ext_map_prod_taxioms:
  lf_axiom (fun x => Lg I (ext_map_prod_aux x f))
    (productf I src) (productf I trg).
Proof. 
move=>  x /setXf_P [pa pb pc]; apply/setXf_P; split;aww.
rewrite /ext_map_prod_aux  => i iI; rewrite LgV //.
move : (ax iI) => [fi dfi sr]; apply: sr.
by apply: inc_V_range=>//;rewrite dfi;  apply: pc. 
Qed.

Lemma ext_map_prod_f : function (ext_map_prod I src trg f).
Proof. by apply: lf_function; apply:  ext_map_prod_taxioms. Qed.

Lemma ext_map_prod_V x: inc x (productf I src) ->
  Vf (ext_map_prod I src trg f) x = Lg I (ext_map_prod_aux x f).
Proof. move => h; rewrite LfV //; apply: ext_map_prod_taxioms. Qed.

Lemma ext_map_prod_VV x i:
  inc x (productf I src) -> inc i I ->
  Vg (Vf (ext_map_prod I src trg f) x) i = Vg (f i) (Vg x i) .
Proof. move=> xp iI; rewrite ext_map_prod_V // LgV //. Qed.

End ExtMapProd.

Lemma ext_map_prod_composable I p1 p2 p3  g f h:
  ext_map_prod_axioms I p1 p2 f ->
  ext_map_prod_axioms I p2 p3 g -> 
  (forall i, inc i I -> h i = (g i) \cf (f i)) ->
  (forall i, inc i I -> (g i) \cfP (f i)) ->
  ext_map_prod_axioms I p1 p3 h.
Proof. 
move=> emp1 emp2 alh alfc x xs.
move: (emp1 _ xs) (emp2 _ xs) => [fgg dg srg] [fgf df srf].
move: (alfc _ xs)(alh _ xs) => fca ->.
have fgc: fgraph ((g x) \cf (f x)) by apply: composef_fgraph. 
have dfc :domain((g x) \cf (f x)) = domain (f x) by rewrite /composef; aw.
rewrite dfc dg; split=>//.
move=> y /(range_gP fgc) [z zdg ->];rewrite composef_ev //; last by ue.
apply: srf; apply/(range_gP fgf); exists  (Vg (f x) z) => //. 
rewrite df; apply: srg; apply: inc_V_range =>//; ue. 
Qed.

Lemma ext_map_prod_compose I p1 p2 p3  g f h:
  ext_map_prod_axioms I p1 p2 f ->
  ext_map_prod_axioms I p2 p3 g ->
  (forall i, inc i I -> h i = (g i) \cf (f i)) ->
  (forall i, inc i I -> (g i) \cfP (f i)) ->
  (ext_map_prod I p2 p3 g) \co (ext_map_prod I p1 p2 f) =
  (ext_map_prod I p1 p3 h).
Proof.
move=> emp1 emp2 alh alfc. 
set f1:= (ext_map_prod I p2 p3 g).
set f2:= (ext_map_prod I p1 p2 f). 
set f3:= (ext_map_prod I p1 p3 h).
move: (ext_map_prod_composable emp1 emp2 alh alfc) => emp3.
have cee: (f1 \coP f2).
  split; first by apply: ext_map_prod_f. 
     by apply: ext_map_prod_f. 
  by rewrite /f1/f2/ext_map_prod; aw.
have fcee: (function (f1 \co f2)) by fct_tac.
have sf23: source f2 = source f3.
  by rewrite /f2 /f3/ext_map_prod; aw.
have tf13: target f1 = target f3.
  by rewrite /f1 /f3/ext_map_prod; aw.
apply: function_exten; aw => //. 
  by apply: ext_map_prod_f =>//.
move=> x xs; rewrite compfV //.
have xp: inc x (productf I p1) by move: xs; rewrite /f2/ext_map_prod; aw.
set t:= Vf f2 x.
have tv: t = Lg I (ext_map_prod_aux x f) by rewrite /t/f2 ext_map_prod_V //.
have ->: (Vf f1 t =  Lg I (ext_map_prod_aux t g)). 
  rewrite /f1 ext_map_prod_V //.
  have tf2: (target f2 = productf I p2) by rewrite/f2/ext_map_prod; aw.
  rewrite/t -tf2; Wtac.
  by rewrite/f2; apply: ext_map_prod_f =>//.
have ->: Vf f3 x = Lg I (ext_map_prod_aux x h) by rewrite/f3 ext_map_prod_V. 
apply: Lg_exten => e ei; rewrite tv /ext_map_prod_aux. rewrite LgV //.
have aux:= (alfc _ ei).
rewrite (alh _ ei) composef_ev // (proj32 (emp1 _ ei)).
by move /setXf_P: xp => [_ dx]; apply.
Qed.

Lemma ext_map_prod_fi I p1 p2 f:
  ext_map_prod_axioms I p1 p2 f ->
  (forall i, inc i I -> injective_graph (f i)) ->
  injection (ext_map_prod I p1 p2 f).
Proof. 
move=> emp alli; split; first by apply: ext_map_prod_f. 
rewrite /ext_map_prod lf_source  => x y xp yp eql.
apply: (setXf_exten xp yp) =>i iI.
move: (ext_map_prod_VV emp xp iI); move: (ext_map_prod_VV emp yp iI).
rewrite eql; move=> -> aux.
move: (emp _ iI)=> [_ df sr].
move: (alli _ iI) => [ff]; apply =>//; rewrite df.
  by move: xp=> /setXf_P [_ dx];  apply. 
by move /setXf_P: yp  => [_ dx];  apply.
Qed.

Lemma ext_map_prod_fs I p1 p2 f: (* AC *)
  ext_map_prod_axioms I p1 p2 f ->
  (forall i, inc i I -> range (f i) = p2 i) ->
  surjection (ext_map_prod I p1 p2 f).
Proof.
move=> emp als;
set g :=(ext_map_prod I p1 p2 f).
have fg: function g by apply: ext_map_prod_f. 
split => //.
have semp: source g = productf I p1 by rewrite /g /ext_map_prod lf_source.
have temp: target g = productf I p2 by rewrite /g /ext_map_prod lf_target.
rewrite semp temp; move=> y yt.
have ext: (forall i, inc i I -> exists2 z, inc z (p1 i) & Vg y i = Vg (f i) z).
  move=> i iI; move: (emp _ iI) => [ff df sr].
  move /setXf_P : yt => [fy dy ip2]; move: (ip2 _ iI).
   by rewrite - (als _ iI);  move/(range_gP ff); rewrite df.
pose pr i:= (fun z => inc z (p1 i) /\ Vg y i = Vg (f i) z).
set x:= Lg I (fun i => choose (pr i)).
have xp: forall i, inc i I -> pr i (Vg x i).
  move=> i iI;  rewrite LgV//; apply: choose_pr. 
  by move: (ext _ iI) => [s xa xb]; exists s.
have ixp: (inc x (productf I p1)).
  apply/setXf_P; rewrite /x; split; aww; rewrite -/x.
  by move=> i iI; aw; move: (xp _ iI) => [].  
have xsq: (inc x (source g)) by ue. 
have iWp: (inc (Vf g x)(productf I p2)) by rewrite -temp; Wtac.
ex_tac; symmetry;apply: (setXf_exten  iWp yt); move=> i iI /=. 
by rewrite ext_map_prod_VV //;move: (xp _ iI) => [].
Qed.

Lemma fun_set_to_prod1 F f i:
  fgraph F -> inc i (domain F) ->
  function f -> target f = productb F -> 
  function_prop (pr_i F i \co f) (source f) (Vg F i) /\
   (forall x, inc x (source f) ->  Vf (pr_i F i \co f) x = Vg (Vf f x) i).
Proof.
move=> fF id ff tfpF.
have aux: (pr_i F i) \coP f. 
  split => //; [by apply: pri_f=>// | by symmetry; rewrite /pr_i; aw].
rewrite /function_prop {2 3} /pr_i; aw; split.
  by saw; fct_tac.
move=> x xs; rewrite compfV //; rewrite pri_V //; rewrite -tfpF; fprops.
Qed.

(** The two sets (prod Fi)^E and prod (Fi^E) are isomorphic *)

Definition fun_set_to_prod src F :=
  Lf (fun f => 
       Lg (domain F)( fun i=> (graph ( (pr_i F i) \co
          (triple src (productb F) f)))))
     (gfunctions src (productb F))
    (productb (Lg (domain F) (fun i=> gfunctions src (Vg F i)))).

Section FunSetToProd.
Variables  (src F: Set).
Hypothesis (fF: fgraph F).

Lemma fun_set_to_prod2 f gf:
  inc gf (gfunctions src (productb F)) ->
  f = (triple src (productb F) gf) -> function_prop f src (productb F).
Proof. 
move=> igf eq.
have [g [fg sg tg gg]] := (gfunctions_hi igf).
have -> //  : f = g.
by rewrite eq - sg -tg -gg; apply: corresp_recov1; move: fg=> [ res _]. 
Qed.

Lemma fun_set_to_prod3:
  lf_axiom(fun f => 
       Lg (domain F)( fun i=> (graph (compose (pr_i F i)
          (triple src (productb F) f)))))
     (gfunctions src (productb F))
    (productb (Lg (domain F) (fun i=> gfunctions src (Vg F i)))).
Proof. 
move=> x xs.
set (f:= triple src (productb F) x).
move: (fun_set_to_prod2 xs  (refl_equal f)) => [ff sf tf].
apply/setXf_P;split; aww => i id; rewrite LgV //.
move: (fun_set_to_prod1 fF id ff tf) => [[fc sc tg] vc].
rewrite -/f - sf - sc -tg; apply: gfunctions_i; fprops.
Qed.

Lemma fun_set_to_prod4 : 
  function_prop (fun_set_to_prod src F) (gfunctions src (productb F))
  (productb (Lg (domain F) (fun i=> gfunctions src (Vg F i)))).
Proof. 
rewrite/fun_set_to_prod; hnf;aw; split => //.
by apply: lf_function; apply: fun_set_to_prod3.
Qed.

Definition fun_set_to_prod5 F f :=
  ext_map_prod (domain F) (fun i=> source f)(fun i=> Vg F i) 
  (fun i => (graph (compose (pr_i F i) f))).

Lemma fun_set_to_prod6 f:
  function f -> target f = productb F -> 
  (function (fun_set_to_prod5 F f) /\ 
    (fun_set_to_prod5 F f) \coP (constant_functor (domain F)(source f) )/\ 
    (fun_set_to_prod5 F f) \co (constant_functor (domain F)(source f)) =f).
Proof. 
move=> ff tfpF.
set (tf := fun_set_to_prod5 F f). 
have ftf: function tf.
  rewrite /tf/fun_set_to_prod5; apply: ext_map_prod_f=> x xs. 
  have [[fc sc tc] vc] := (fun_set_to_prod1 fF xs ff tfpF).
  split.
  + fprops.
  + by rewrite domain_fg.
  + by rewrite -tc; apply: f_range_graph.
have  ttf:(productb F = target tf). 
  rewrite /tf/fun_set_to_prod5/ext_map_prod. 
  aw; rewrite /productf;  apply: f_equal; apply: fgraph_exten; aww. 
  by move=> x xd; rewrite LgV.
have ctf: tf \coP (constant_functor (domain F)(source f)).
  split; fprops.   
    rewrite /constant_functor; apply: lf_function. 
    move => x xs /=; apply/gfunctions_P2. 
    rewrite/cst_graph; aw;split; fprops.
    have aux: fgraph (Lg (domain F) (fun _ : Set => x)) by fprops.
    move=> y /(range_gP aux) [b ]; rewrite Lgd => h ->; rewrite LgV //.
  set (k:= cst_graph (domain F) (source f)); aw.
  have: (domain F = domain k) by rewrite/k; aw.
  move=> ->; rewrite /constant_functor; aw.
  rewrite - setXb_eq_gfunctions.
      by rewrite /tf/fun_set_to_prod5/ext_map_prod; aw.
  by rewrite /k; aw => i id; rewrite LgV.
split=> //; split=>//.
have ta1: lf_axiom [eta cst_graph (domain F)]
   (source f) (gfunctions (domain F) (source f)).
  move=> y yd; rewrite /gfunctions. 
  apply: Zo_i; last by aw; split; fprops.
  apply /setP_P => t /funI_P [z zd ->]; fprops.
symmetry; apply: function_exten =>//; try fct_tac. 
    by rewrite /constant_functor; aw.
  rewrite /tf/fun_set_to_prod5/ext_map_prod; aw.
  by rewrite /productf tfpF Lg_recovers //.
move=> x xsf; rewrite /constant_functor.
rewrite compfV // ?lf_source // LfV //.
have cgd: inc (cst_graph (domain F) x)
     (productf (domain F) (fun _ : Set => source f)).
  rewrite/cst_graph; apply/setXf_P.
  by split; aww => j jd; rewrite LgV.
have:inc (Vf f x) (productb F) by rewrite - tfpF; fprops.
have: (inc (Vf tf (cst_graph (domain F) x)) (productb F)).
  by rewrite ttf; Wtac; rewrite /tf/fun_set_to_prod5/ext_map_prod; aw.
move=> p1 p2; apply: (setXb_exten p2 p1).
move=> i idf /=; rewrite /tf/fun_set_to_prod5  ext_map_prod_V //. 
  rewrite LgV // /ext_map_prod_aux /cst_graph   LgV //.
  set cp:= (pr_i F i) \co f.
  rewrite -/(Vf cp x) /cp compfV //; first by rewrite pri_V.
  split => //; [ by apply: pri_f |  by rewrite /pr_i; aw].
move => j jd.
move: (fun_set_to_prod1 fF jd ff tfpF) => [[fcf sc tc] vc].
split; fprops; first by  rewrite - sc; fprops; rewrite domain_fg//.
by rewrite -tc;apply: f_range_graph=>//. 
Qed.

Lemma fun_set_to_prod7 f g:
  (forall i, inc i (domain F) -> inc (f i) (gfunctions src (Vg F i))) ->
  g = ext_map_prod (domain F) (fun i=> src)(Vg F) f ->
  (forall i, inc i (domain F) ->
    f i = graph ((pr_i F i) \co (g \co (constant_functor (domain F) src) ))).
Proof. 
move=> allf geq i idf.
set f1:= (constant_functor (domain F) src).
have fct: function f1.
  apply: lf_function. 
  move=> x xd; apply/ gfunctions_P2; rewrite /cst_graph.
  by split; aww; move => w /Lg_range_P [b _ ->].
have fg: (function g). 
  rewrite geq; apply: ext_map_prod_f. 
  move=> x xd; move:(gfunctions_hi (allf _ xd))=> [h [fh sh <- <-]]. 
  by rewrite domain_fg //; split; fprops;apply: f_range_graph.
have cpa: g \coP f1.
  split=>//;rewrite geq/f1/ext_map_prod/constant_functor; aw. 
  rewrite /productf. 
  set k:= cst_graph (domain F) src. 
  have dkdf: (domain k = domain F) by rewrite /k;aw. 
  have aux: (forall i, inc i(domain k) -> Vg k i = src). 
    by move=> j jd; rewrite /k LgV //;ue.
  by rewrite (setXb_eq_gfunctions aux) dkdf.
have fcf: function (g \co f1) by fct_tac.
have cpb: (pr_i F i) \coP (g \co f1).
  split => //; first by apply: pri_f.
  rewrite geq /pr_i/ext_map_prod; aw; rewrite/productf Lg_recovers //.
have fctr: function ((pr_i F i) \co (g \co f1)) by fct_tac.
have [h [fh sh th gh]] := (gfunctions_hi (allf _ idf)).
have sf1: source f1 = source h by rewrite /f1/pr_i/constant_functor; aw.
have ta1: lf_axiom  (cst_graph (domain F)) src (gfunctions (domain F) src).
  move=> y yd; rewrite /cst_graph/gfunctions. 
  apply: Zo_i; last by aw;  split; fprops.
  apply /setP_P => t /funI_P [z zd ->]; fprops.
suff: (h =  (pr_i F i) \co (g \co f1)) by move=> <-; ue.
apply: function_exten =>//.
    by rewrite /pr_i/constant_functor; aw.
  by rewrite /pr_i/constant_functor; aw.
rewrite /f1; move => x xh. 
have xs: inc x src by  rewrite - sh.
have xs2: inc x (source (constant_functor (domain F) src)).
  by rewrite /constant_functor; aw.
have aax: ext_map_prod_axioms (domain F) (fun _ : Set => src)(Vg F) f.
  move=> z zs; move: (gfunctions_hi (allf _ zs))=> [k [fk <- <- <-]]. 
  by rewrite  domain_fg //;split; fprops; apply: f_range_graph.
set q:= cst_graph (domain F) x.
have qp: inc q  (productf (domain F) (fun _ : Set => src)).
  by apply/setXf_P; rewrite/q; aw; split; fprops => k kd; rewrite LgV.
have si: Vf (constant_functor (domain F) src) x = q.
  rewrite /Vf/constant_functor /Lf; aw; rewrite LgV//.
have seq: (x = Vg q i) by  rewrite LgV.
rewrite ! compfV // ?compf_s //   si geq ext_map_prod_V //.
set s:= (Lg (domain F) (ext_map_prod_aux q f)).
have isp: inc s (productb F). 
  rewrite /s /ext_map_prod_aux; apply/setXb_P; split;aww.
  move=> j jd; rewrite LgV // LgV //. 
  have [k [fk sk <- <-]] := (gfunctions_hi (allf _ jd)). 
  rewrite -/(Vf _ _ ); Wtac. 
by rewrite /s pri_V // LgV //  /ext_map_prod_aux /Vf gh - seq.
Qed.

Lemma fun_set_to_prod8: bijection (fun_set_to_prod src F).
Proof. 
move: (fun_set_to_prod4); set (g :=fun_set_to_prod src F).
move => [fg sg tg]. 
split.
  split =>// x y; rewrite sg => xs ys.
  have [x0 [fx0 sx0 tx0 gx]] := (gfunctions_hi xs).
  have [x1 [fx1 sx1 tx1 gx1]] := (gfunctions_hi ys).
  have ta:=(fun_set_to_prod3).
  rewrite /g/fun_set_to_prod ! LfV //; clear ta; move => eq.
  rewrite - gx - gx1; congr graph.
  apply: function_exten=>//; (try  ue) => x2 x2s.
  apply: (setXb_exten (f := F)); [ ue| rewrite sx0 - sx1 in x2s; ue |]. 
  move=> i iF.
  have [[fc0 sc0 tc0] vc0] := (fun_set_to_prod1 fF iF fx0 tx0).
  have [[fc1 sc1 tc1] vc1] := (fun_set_to_prod1 fF iF fx1 tx1).
  have x0c: (x0 = triple src (productb F) x).
    by rewrite - sx0 -tx0 -gx corresp_recov1 //; move: fx0=>[cx0 _].
  have x1c: (x1 = triple src (productb F) y).
    by rewrite - sx1 -tx1 -gx1 corresp_recov1 //; move: fx1=>[cx1 _].
  have cc: ((pr_i F i) \co x0 =  (pr_i F i) \co x1). 
    move: (congr1 (Vg ^~i) eq). rewrite !LgV //  - x0c -x1c => eq1.
    by apply: function_exten1 =>//; aw.
  by rewrite - vc0  //; rewrite sx0 - sx1 in x2s; rewrite cc - vc1.
split => // y.
rewrite sg  {1} /g /fun_set_to_prod lf_target. 
move/setXf_P=> [fy]; aw; move=> dy py.
set (x:= Lf (fun u=> Lg (domain F) (fun i=> Vg (Vg y i) u)) src (productb F)).
have sx: source x = src  by rewrite /x; aw. 
have tx: target x = productb F by rewrite /x; aw. 
have fx: function x.
  rewrite /x; apply: lf_function. 
  move=> t ts; apply/setXb_P; split; aww.
  move => i idf; rewrite LgV //; move: (py _ idf); aw=> xpp.
  have [k [fk sk <- gk]] := (gfunctions_hi xpp).
  have ->: (Vg (Vg y i) t = Vf k t) by rewrite /Vf gk. 
  Wtac.
have gs: inc (graph x) (gfunctions src (productb F)). 
  rewrite - sx -tx; apply: gfunctions_i=> //. 
ex_tac.
move: (fun_set_to_prod3) => ax.  
rewrite /g/fun_set_to_prod; rewrite LfV //; clear ax.
symmetry;apply: fgraph_exten; aw;fprops =>//.
move=> z zd; rewrite LgV //;move: (py _ zd); aw; move => Vzg.
have xp: (x = triple src (productb F) (graph x)). 
  by rewrite - sx -tx corresp_recov1 //; move: fx=>[cx _].
rewrite - xp.
have [x1 [fx1 sx1 tx1 gx1]] := (gfunctions_hi Vzg).
suff: (x1 = (pr_i F z) \co x) by move => <-.
apply: function_exten =>//; try fct_tac; try (rewrite /pr_i; aw;  ue).
  by apply: pri_f.
move =>// x0 z0s.
have x0s: inc x0 src by ue.
have x0s': inc x0 (source x) by ue.
have cc: (pr_i F z) \coP x.
split => //; [apply: pri_f=>//| rewrite /pr_i; aw; ue].  
have Wp: inc (Vf x x0) (productb F) by Wtac.
rewrite compfV // pri_V // /x LfV //.
  rewrite LgV // /Vf; ue.  
move=> t ts /=; apply /setXb_P; split;aww.
move=> i id; aw; move: (py _ id); aw => aux. 
move: (gfunctions_hi aux) => [x2 [fx2 sx2 tx2 gx2]].
rewrite LgV // -tx2 -gx2 - [Vg _  _] /(Vf x2 t); Wtac.
Qed.

End FunSetToProd.

End Bproduct. 

Export Bproduct.   

