(** * Theory of Sets  EIII-3   Equipotents Sets. Cardinals
  Copyright INRIA (2009-2013 2018) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset7.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Export sset6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Bordinal.


(** ** Ordinals *)

(** We start with some properties of a set; 
[ordinal_oa] and [ordinal_o] are orderings  *)

Definition transitive_set E:= forall x, inc x E -> sub x E.
Definition decent_set E := forall x, inc x E -> ~ (inc x x).
Definition trans_dec_set E := transitive_set E /\ decent_set E.
Definition asymmetric_set E := 
  forall x y, inc x E -> inc y E -> inc x y -> inc y x -> False.
Definition ordinal_oa :=  graph_on (fun a b => inc a b \/ a = b).
Definition ordinal_o := sub_order.
Definition osucc x := x +s1 x.

Lemma succ_i x: inc x (osucc x).
Proof. by apply:setU1_1.  Qed.

Hint Resolve succ_i: fprops.

Lemma transitive_setP x: transitive_set  x <-> sub (union x) x.
Proof.
split; first by move => h  t/setU_P [y ty] /h; apply.
move => s y yx t ty; apply: s; union_tac.
Qed.

Lemma transitive_setU x: alls x transitive_set -> transitive_set (union x).
Proof. 
move=> alt a /setU_hi [y ay yx] t ta.
move: (((alt _ yx) _ ay) _ ta) => ty; union_tac.
Qed.

Lemma irreflexive_decent X: decent_set X -> ~ (inc X X).
Proof. move => ha hb; exact(ha _ hb hb). Qed.
  
Lemma trans_dec_setU x: alls x trans_dec_set ->  trans_dec_set (union x).
Proof. 
move=> alt; split.
  by apply: transitive_setU => y /alt []. 
by move=> a /setU_hi [y ay yx] aa; case: ((proj2 (alt _ yx)) _ ay).
Qed.

Lemma trans_dec_setI x: alls x trans_dec_set -> trans_dec_set (intersection x).
Proof.
case: (emptyset_dichot x).
  by move => -> _; rewrite setI_0; split => t /in_set0.
move=> nea alt; split.
  move=> a au t ta; apply: (setI_i nea) => y yx.
  exact: ((proj1 (alt _ yx)) _  (setI_hi au yx)).
move: nea=> [y yx] a au; exact: (proj2 (alt _ yx) _  (setI_hi au yx)).
Qed.

Lemma osucc_prop (p: property) x: p x -> alls x p -> alls (osucc x) p.  
Proof.
by move => px pxx t /setU1_P; case; [ move/pxx | move -> ].
Qed.

Lemma trans_dec_succ y: trans_dec_set y -> trans_dec_set (osucc y).
Proof. 
move => [tsy dsy]; split. 
  apply: osucc_prop; first by apply:setU1_r.
  by move => z zy t  /(tsy _ zy) ty; apply:setU1_r.
exact:(osucc_prop (irreflexive_decent dsy) dsy).
Qed.

(** Definition of an ordinal; set such sets are transitive and decent *)

Definition ordinalp X:=
   forall Y, sub Y X -> transitive_set Y -> Y <> X -> inc Y X.

Notation "f =1o g" := (forall x, ordinalp x -> f x = g x)
  (at level 70, format "'[hv' f '/ '  =1o  g ']'", no associativity).
Definition ordinal_fam g := allf g ordinalp.
Definition ordinal_set E :=  alls E ordinalp.


Lemma OS_succ x: ordinalp x -> ordinalp (osucc x).
Proof.
move=> ox y ytx tsy yntxx.
case: (equal_or_not y x) => yx; first by rewrite yx; fprops.
apply: setU1_r; apply:(ox _ _ tsy yx) => t ty.
case /setU1_P: (ytx _ ty) => // tx; rewrite tx in ty.
by case: yntxx; apply: (extensionality ytx); apply: setU1_sub => //; apply: tsy.
Qed.

Hint Resolve OS_succ : fprops.

Lemma ordinal_trans_dec x: ordinalp x -> trans_dec_set x. 
Proof. 
move=> ox.
set y := Zo (\Po x) trans_dec_set.
set t := union y.
have: trans_dec_set t by apply: trans_dec_setU=> z /Zo_hi.
case: (equal_or_not t x); first by move=> ->.
move=> ntx tct; move: (trans_dec_succ tct) => tcst.
have stx: sub t x by apply: setU_s2 =>z /Zop_S. 
have itx:= (ox _ stx (proj1 tct) ntx).
case: ((proj2 tcst) _ (succ_i t)).
by apply: (setU_i (succ_i t)); apply: Zop_i => //; apply: setU1_sub.
Qed.

Lemma ordinal_transitive x: ordinalp x -> transitive_set x.
Proof. by move /ordinal_trans_dec => []. Qed.

Lemma ordinal_decent x: ordinalp x -> decent_set x.
Proof. by move /ordinal_trans_dec => []. Qed.

Lemma ordinal_irreflexive x: ordinalp x -> ~ (inc x x).
Proof. by move/ordinal_decent  /irreflexive_decent. Qed.

(** For ordinals [inc] is the same as  [strict_sub] *)

Lemma ordinal_sub x y:
  ordinalp x -> ordinalp y -> sub x y ->
  x = y \/ inc x y.
Proof. 
move=> ox oy xy; alt_tac nxy.
exact: (oy _ xy (ordinal_transitive ox) nxy).
Qed.

Lemma ordinal_sub2 x y: ordinalp y ->
  inc x y -> ssub x y.
Proof.
move=> /ordinal_trans_dec [ty dy xy]; split; first by apply: ty. 
by move => ac; case: (dy _ xy); rewrite {2} ac.
Qed.

Lemma ordinal_sub3 x y: ordinalp y ->
  inc x (osucc y) -> sub x y.
Proof.  
by move => /ordinal_transitive yb; apply: (osucc_prop (p := sub ^~y)).
Qed.

Lemma ordinal_sub4P x y: ordinalp x ->  ordinalp y ->
  (sub x y <-> inc x (osucc y)).
Proof.  
move=> ox oy; split; last by apply: ordinal_sub3. 
by case /(ordinal_sub ox oy) => H; apply/setU1_P; [right | left].
Qed.

(** The intersection of a set of ordinal is in the set; 
we deduce the trichotomy property, which says that [sub] is a total ordering for ordinals *)

Lemma ordinal_setI x: nonempty x -> ordinal_set x ->
   inc (intersection x) x.
Proof.
move=> nex alo; ex_middle nix.
have [tic dix]: (trans_dec_set (intersection x)).
  apply: trans_dec_setI => y yx; exact: (ordinal_trans_dec (alo _ yx)).
case:(irreflexive_decent dix).
apply: (setI_i nex)=> a ax; apply: (alo _ ax _ (setI_s1 ax) tic); dneg xx; ue.
Qed.

Lemma ordinal_inA x y:
  ordinalp x -> ordinalp y -> 
  [\/ inc x y, inc y x | x = y].
Proof.
move=> ox oy.
have aux: (ordinal_set (doubleton x y)) by move=> a /set2_P [] ->.
case /set2_P: (ordinal_setI (set2_ne x y) aux).
  move/setI2id_Pl => h;case: (ordinal_sub ox oy h) => p; in_TP4.
move/setI2id_Pr => h;case: (ordinal_sub oy ox h); in_TP4.
Qed.

(** [X] is an ordinal if it is transitive and its elements are ordinals;
or if it is the successor of an ordinal *)

Lemma ordinal_pr x: transitive_set x -> ordinal_set x ->
  ordinalp x.
Proof. 
move=> tx alo y syx ty nyx.
move: (setC_ne (conj syx nyx)) =>[z /setC_P [zx nzy]]; move: (alo _ zx)=> oz.
have zy: (sub y z).
  move=> t ty'; move: (alo _ (syx _ ty'))=> ot. 
  case:(ordinal_inA oz ot) => zt // ;case:nzy; [ by apply: (ty _ ty')| ue].
case: (equal_or_not y z); first by move=> ->.
move=> yz; apply: (tx _ zx _ (oz _ zy ty yz)).
Qed.

(** Any element of an ordinal is an ordinal, in particular, 
if the successor of [x] is an ordinal, so is [x]; 
and no set contains all ordinals *)


Lemma Os_ordinal x: ordinalp x -> ordinal_set x.
Proof. 
move=> ox.
set t:= union (Zo(\Po x) (fun y=> transitive_set y /\ ordinal_set y)).
have tp: ordinal_set t by move => z /setU_P [v zv /Zo_hi [_]]; apply.
have ot: ordinalp t. 
  by apply: ordinal_pr=> //;apply: transitive_setU; move=> t' /Zo_hi [pb _].
case: (ordinal_inA ox ot); last by move => ->.
  move=> /setU_P [v xv /Zop_S aux].
  case: (ordinal_irreflexive ox (aux _ xv)).
move => tx.
case: (ordinal_irreflexive ot).
apply: (@setU_i _ (t +s1 t)); [fprops | apply: Zop_i ].
  by apply:setU1_sub => //; apply: (ordinal_transitive ox).
split; first by apply: (ordinal_transitive (OS_succ ot)).
by move=> u /setU1_P; case; [ apply: tp |move=> ->// ].
Qed.

Lemma OS_succr x: ordinalp (osucc x) -> ordinalp x.
Proof. move=> os ; apply: (Os_ordinal os); fprops. Qed.

Lemma Os_sub x y: ordinal_set x -> sub y x -> ordinal_set y.
Proof. by move => ha hb t /hb /ha. Qed.

Lemma Os_funI x h:
  (forall t, inc t x -> ordinalp (h t)) -> ordinal_set (fun_image x h).
Proof. by move => H t /funI_P [z /H zx ->]. Qed.

Definition non_coll(p: property) := ~ exists E, forall x, inc x E <-> p x.

Lemma non_collP p: non_coll p <->  ~ exists E, forall x, p x -> inc x E.
Proof.
split => h [E Ep]; case:h; last by exists E => x /Ep.
exists (Zo E p)=> x;split; [ by apply:Zo_hi | move => px; apply:Zo_i; fprops].
Qed.

Lemma non_collectivizing_ordinal: non_coll ordinalp.
Proof.
move=> [x xp].
have osx: ordinal_set x by move => t /xp.
have yo: ordinalp x.
  by apply: ordinal_pr => // a ay b ba; move/xp: (Os_ordinal (osx _ ay) ba).
by case:(ordinal_irreflexive yo); apply/xp.
Qed.

(** Since an ordinal is irreflexive it is asymmetric, and the successor function is injective *)

Lemma osucc_inj : { when ordinalp &,  injective osucc }.
Proof.
move=> a b oa ob eq.
have /setU1_P [ab | //]: inc a (osucc b) by rewrite -eq; fprops.
have /setU1_P [ba | //]: inc b (osucc a) by rewrite eq; fprops.
case: (ordinal_irreflexive oa (ordinal_transitive oa ba ab)).
Qed.

Lemma ordo_leP x a b: 
  gle (ordinal_o x) a b <-> [/\ inc a x, inc b x & sub a b].
Proof. apply: sub_gleP. Qed.

Lemma ordo_ltP x a b: ordinalp x -> inc a x -> inc b x ->
   (glt (ordinal_o x) a b <-> inc a b).
Proof.
move=> ox ax bx.
have ob:= (Os_ordinal ox bx).
split. 
  move => [/ordo_leP [_ _  sab]] nab.
  by case: (ordinal_sub (Os_ordinal ox ax) ob sab).
by move => /(ordinal_sub2 ob) [sab nab]; split => //;apply /ordo_leP.
Qed.

(** If [p x] holds for some ordinal, 
  then [p] holds for a least ordinal (for [sub]) *)

Definition least_ordinal (p: property) x:= intersection (Zo (osucc x) p).

Lemma least_ordinal1 x (p: property) (y:= least_ordinal p x) :
  ordinalp x -> p x -> 
    [/\ ordinalp y, p y & forall z, ordinalp z -> p z -> sub y z].
Proof.
move=> ox px.
set (t:= Zo (osucc x) p).
have xt: inc x t by apply :Zo_i; fprops.
have net: nonempty t by exists x. 
have osbx:= (OS_succ ox).
have alo: (ordinal_set t) by apply:(Os_sub (Os_ordinal osbx)); apply: Zo_S.
have h:= (ordinal_setI net alo).
split;[by apply: alo |  by move: h => /Zo_hi | move=> z oz pz ].
have aux: inc z t -> sub y z by move=> zt w wi; apply: (setI_hi wi zt).
case: (ordinal_inA ox oz) => ty.
- exact: (sub_trans (setI_s1 xt) (ordinal_transitive oz ty)).
- by apply: aux; apply: Zo_i => //;apply: setU1_r.
- apply: aux; ue.
Qed.

(** On an ordinal, [inc] and [sub] induce the same ordering, 
which is a well-ordering *)

Lemma ordinaloa_alt x: graph_on (fun a b => inc a (osucc b)) x = ordinal_oa x.
Proof. apply: graph_on_exten => a b _ _; exact:setU1_P. Qed.

Lemma ordinal_same_wo x: ordinalp x ->
  ordinal_o x = ordinal_oa x.
Proof.
move=> ox; rewrite - ordinaloa_alt; apply:  graph_on_exten => a b ax bx.
move:(Os_ordinal ox ax) (Os_ordinal ox bx) => oa ob.
exact :ordinal_sub4P.
Qed.

Lemma ordinal_o_wor x: ordinalp x -> worder (ordinal_o x).
Proof.
move=> ox.
have [pa pb]:= (sub_osr x).
apply: (worder_prop_rev pa); rewrite pb => y yE nex.
have p1:= (Os_sub (Os_ordinal ox)  yE).
have hh: sub y (substrate (sub_order x)) by ue.
have ix:= (ordinal_setI nex p1); ex_tac => z zy.
by apply/ordo_leP;split; [apply: yE | apply: yE | apply: setI_s1 ].
Qed.

Lemma ordinal_worder x: ordinalp x -> worder (ordinal_oa x).
Proof. by move=> ox; rewrite - ordinal_same_wo //; apply: ordinal_o_wor. Qed.

(** If [x] is an element of an ordinal [E], 
  the set of elements less than [x] (for the ordering of [E]) is [x] *)

Lemma ordinal_segment1 E x: trans_dec_set E ->
  inc x E -> segment (ordinal_oa E) x = x.
Proof.
move => [tE dE] xE.
suff: segment (ordinal_oa E) x = x \cap E. 
  by move => ->; apply/setI2id_Pl; apply: tE.
rewrite /segment /ordinal_oa /interval_uo graph_on_sr; last by fprops.
set_extens y.
  by move/Zo_hi => [ /graph_on_P1 [pa pb pc] pd]; apply: setI2_i => //;case: pc.
move /setI2_P=> [yx yE]; apply:(Zo_i yE);split.
  by apply/graph_on_P1; split => //; left.
move=> xy; rewrite xy in yx; case: (dE _ xE yx).
Qed.

Lemma ordinal_segment E x: ordinalp E ->
  inc x E -> segment (ordinal_o E) x = x.
Proof.
move=> ox xE;rewrite ordinal_same_wo //.
by apply: ordinal_segment1 => //; apply: ordinal_trans_dec.
Qed.

(** Alternate definition of an ordinal :
 transitive, asymmetric and [inc] is a well-ordering *)

Lemma ordinal_pr1 E:
  ordinalp E <-> 
  [/\ transitive_set E, worder (ordinal_oa E) & asymmetric_set E].
Proof. 
split.
  move=> oE; split => //.
  - by apply: ordinal_transitive.
  - by apply: ordinal_worder.
  - move=> x y xE yE xy yx.
    have ox:= (Os_ordinal oE xE). 
    have xx:=(ordinal_transitive ox yx xy).
    by case:(ordinal_irreflexive ox xx).
move=> [tE woE aE] X XE tX nXE.
have de: decent_set E by move=> u uE uu; case: (aE _ _ uE uE uu uu).
have p0:forall b, inc b E -> inc b b \/ b = b by move=> b bE; right.
have sg: (substrate (ordinal_oa E)) = E by rewrite /ordinal_oa graph_on_sr.
have si: segmentp (ordinal_oa E) X.
  rewrite /segmentp /interval_uo /ordinal_oa sg; split => //.
  move=> x y xX /graph_on_P1 [yE _ h].
  case: h; [ apply: (tX _ xX) | by  move => -> ].
case: (well_ordered_segment woE si).
  by rewrite sg; move=> eXE.
by rewrite sg; move=> [x xs ->]; rewrite ordinal_segment1.
Qed.

Lemma ordinal_o_sr x: substrate (ordinal_o x) = x.
Proof. exact: (proj2 (sub_osr _)). Qed.

Lemma ordinal_o_or x: order (ordinal_o x).
Proof. exact: (proj1 (sub_osr x)). Qed.

Lemma ordinal_o_tor x: ordinalp x -> total_order (ordinal_o x).
Proof. by move=> or; apply: (worder_total (ordinal_o_wor or)). Qed.

Hint Resolve ordinal_o_or ordinal_o_wor: fprops.

(** Two isomorphic ordinals are equal *)

  
Lemma ordinal_isomorphism_unique x y f:
  ordinalp x -> ordinalp y -> 
  order_isomorphism f (ordinal_o x) (ordinal_o y) ->
  (x = y /\ f = identity x).
Proof. 
move=> ox oy oif.
move: (oif) => [_ _ [[[ff injf] [_ surf]] srcf trgf] pf].
rewrite !ordinal_o_sr in srcf trgf.
have Wt: forall a, inc a x -> inc (Vf f a) y by move => a ax; Wtac.
have prf2:forall a b, inc a x -> inc b x -> (inc a b <-> inc (Vf f a) (Vf f b)).
  move=> a b ax bx.
  apply: (iff_trans (iff_sym (ordo_ltP ox ax bx))).
  rewrite - srcf in ax bx. 
  apply: (iff_trans (order_isomorphism_siso oif ax bx)).
  apply /ordo_ltP=> //; apply: Wt; ue.
rewrite trgf srcf in surf.
case:(all_exists_dichot1 (fun z => Vf f z = z) x) => H.
  suff xy: x = y by split => //; apply:identity_prop0=> //; split => //; ue.
  set_extens t => tx; first by rewrite - (H _ tx) - trgf; Wtac.
  by move: (surf _ tx)=> [z zx ->];rewrite (H _ zx).
move: H =>[u ux up].
pose prop := fun z => inc z x /\ Vf f z <> z. 
have ppu: prop u by [].
move: (least_ordinal1  (Os_ordinal ox ux) ppu).
set z := least_ordinal _ _. move => [oz [zx fz] zle].
have p1: forall a, inc a z -> Vf f a = a.
  move=> a az; ex_middle aux.
  have ax:= (ordinal_transitive ox zx az).
  have aa:= (zle a (Os_ordinal oz az) (conj ax aux)).
  case: (ordinal_decent ox ax  (aa _ az)).
case: fz;case: (ordinal_inA (Os_ordinal oy (Wt _ zx)) oz). 
+ rewrite srcf in injf; move => h.
  exact: (injf _ _ (ordinal_transitive ox zx h) zx (p1 _ h)).
+ move => ww.
  move:(surf _ (ordinal_transitive oy (Wt _ zx) ww)) => [a ax za].
  by move: ww; rewrite {1 3} za => /(prf2 _ _ ax zx) /p1 ->.
+ done.
Qed.

(** Any well-ordered set is isomorphic to an ordinal *)

Lemma ordinal_isomorphism_exists r (f := ordinal_iso r):
  worder r -> order_isomorphism f r (ordinal_o (target f)).
Proof. 
move=> wor;move: (proj1 wor)=> or.
move: (transfinite_defined_pr target wor) => [suf sf vf].
set E:=  substrate r. 
have fa: function f by fct_tac.
have vf1: forall a b, inc a E -> 
  (inc b (Vf f a) <-> (exists2 u, glt r u a & b = Vf f u)).
  move=> a b aE; rewrite (vf _ aE) /restriction1; aw.
  have ssf: sub (segment r a) (source f) by rewrite sf;apply: sub_segment.
  split. 
    by move/(Vf_image_P fa ssf) => [x /segmentP pa pb]; exists x.
  move => [x ua ub]; apply/(Vf_image_P fa ssf). 
  by exists x => //; apply /segmentP.
have incf: (forall a b, gle r a b -> sub (Vf f a) (Vf f b)). 
  move=> a b ab t.
  have aE: (inc a E) by rewrite /E; order_tac. 
  have bE: (inc b E) by rewrite /E; order_tac.
  move/(vf1 _ _ aE) =>[u us h]; apply/(vf1 _ _ bE); exists u => //; order_tac. 
have incf3: forall a b, inc a (source f) -> inc b (source f) -> 
     sub (Vf f a) (Vf f b) -> gle r a b.
  rewrite sf => a b aE bE sab.
  case: (total_order_pr2 (worder_total wor) bE aE) => // ltab.
  pose (Bad:= Zo E (fun x => inc (Vf f x) (Vf f x))).
  have neb: nonempty Bad.
    by exists b;apply: (Zo_i bE); apply: sab; apply/(vf1 _  _ aE); exists b. 
  have BE: sub Bad E by apply: Zo_S.
  move: (worder_prop wor BE neb) => [y /Zo_P [yE iWWy] yp].
  move/(vf1 _ _ yE): (iWWy) =>  [u us Wu].
  have badu: inc u Bad by apply: Zo_i=>//; [rewrite /E;order_tac | ue ].
  move: (yp _ badu) => yu; order_tac. 
have injf: injection f.
  split=>//; move=> x y xsf ysf Wxy. 
  have p1: sub (Vf f x) (Vf f y) by rewrite Wxy; fprops.
  have p2: sub (Vf f y) (Vf f x) by rewrite Wxy; fprops.
  move: (incf3 _ _ xsf ysf p1) (incf3 _ _ ysf xsf p2) => p3 p4; order_tac.
split => //; [fprops | by rewrite ordinal_o_sr | move=> x y xsf ysf].
split; first by move => pa; apply/ordo_leP;split => //; try Wtac; apply: incf.
move/ordo_leP => [_ _ xy]; apply: (incf3 _ _ xsf ysf xy).
Qed.

(** [ordinal r] is the unique ordinal isomorphic to [r] *)

Definition ordinal r := target (ordinal_iso r).


Lemma OS_ordinal r: worder r -> ordinalp (ordinal r).
Proof.
move => wor.
move => X ha hb.
move: (proj1 wor)=> or.
move: (transfinite_defined_pr target wor).
set f := (transfinite_defined r target); move => [suf sf vf].
set E:=  substrate r. 
have ff: function f by fct_tac.
have H x: inc x E ->  Vf f x = Vfs f (segment r x).
  by move /vf; rewrite /restriction1; aw.
pose A := Zo E (fun z => inc (Vf f z) X).
have Ha: segmentp r A.
  split;first by apply: Zo_S.
  move => x y xA lxy; case: (equal_or_not y x) => ltxy; first by ue.
  have yE: inc y E by rewrite /E; order_tac.
  move  /Zo_P:xA => [xE fbX]; apply: (Zo_i yE); apply: (hb  _ fbX).
  have ssf: sub (segment r x) (source f) by rewrite sf;apply: sub_segment.
  rewrite (H _ xE).
  by apply/(Vf_image_P ff ssf); exists y => //; apply /segmentP.
have sas: sub A (source f) by rewrite sf; apply: Zo_S.
have <-:  Vfs f A = X.
  set_extens t; first by move/(Vf_image_P ff sas) =>[u /Zo_hi ua ->].
  move => tX; apply/(Vf_image_P ff sas).
  move: (proj2 suf _ (ha _ tX)) =>[u usf eq1]; exists u => //.
  by apply: Zo_i; [rewrite /E - sf | ue]. 
case: (well_ordered_segment wor Ha).
  by move ->; rewrite  /ordinal - (surjective_pr0 suf) - sf .
by move =>[a aE ->] _;rewrite -(H a aE); apply: (Vf_target ff); ue.
Qed.


Lemma ordinal_o_is r: worder r -> r \Is (ordinal_o (ordinal r)).
Proof.
move=> wor; move: (ordinal_isomorphism_exists wor) => h. 
by exists (ordinal_iso r).
Qed.

Lemma ordinal_o_o x: ordinalp x -> ordinal (ordinal_o x) = x.
Proof.
move=> ox; move: (ordinal_o_wor ox) => woi.
have h := (ordinal_isomorphism_exists woi).
exact:(esym (proj1 (ordinal_isomorphism_unique ox (OS_ordinal woi) h))).
Qed.

Lemma ordinal_o_isu x y:
  ordinalp x -> ordinalp y -> 
  (ordinal_o x) \Is (ordinal_o y) ->  x = y.
Proof. 
move=> ox oy [f fi]; exact:proj1 (ordinal_isomorphism_unique ox oy fi).
Qed.

Lemma ordinal_o_isu1 r r': worder r -> worder r' ->
  r \Is r' -> ordinal r = ordinal r'.
Proof.
move=> w1 w2 or.
move: (OS_ordinal w1)(OS_ordinal w2) => o1 o2.
move: (ordinal_o_is w1)(ordinal_o_is w2) => i1 i2.
exact: (ordinal_o_isu o1 o2 (orderIT (orderIT (orderIS i1) or) i2)).
Qed.

Lemma ordinal_o_isu2 r x: worder r -> ordinalp x ->
  r \Is (ordinal_o x) -> ordinal r = x.
Proof.
move=> wo ox oi.
by rewrite (ordinal_o_isu1 wo (ordinal_o_wor ox) oi) (ordinal_o_o ox).
Qed. 

Definition the_ordinal_iso r := inverse_fun (ordinal_iso r).

Lemma the_ordinal_iso1 r : worder r -> 
  order_isomorphism (the_ordinal_iso r) (ordinal_o (ordinal r)) r.
Proof.
move=> wor; exact(inverse_order_is (ordinal_isomorphism_exists wor)). 
Qed.

Lemma the_ordinal_iso2 r g:
  worder r -> order_isomorphism g (ordinal_o (ordinal r)) r ->
  g = the_ordinal_iso r.
Proof.
move =>wor; move: (the_ordinal_iso1 wor) => is1 is2.
by rewrite (iso_unique_bis wor is1 is2).
Qed. 

(** We can compare two orderings; this is compatible with order isomorphism.
If [E] and [E'] are two ordinals ordered by [r] and [r'], then
[ordinal_leD1 E E']  says [r <= r']. In this case we have [r <= r'] 
iff [r] is isomorphic to a segment of [r'].
We have [r < r'] iff  [r] is isomorphic to [segment r' x] for some [x]. *)


Definition order_le r r' :=
  [/\ order r, order r' &
  exists f x, 
      sub x (substrate r') /\ order_isomorphism f r (induced_order r' x)].
Notation "x <=O y" := (order_le x y) (at level 60).

Lemma order_leR x: order x -> x <=O x.
Proof.
move=> ox; split => //; exists (identity (substrate x)), (substrate x).
have ss:= (@sub_refl (substrate x)).
have [pa pb]:=(iorder_osr ox ss).
by rewrite (iorder_substrate ox); split => //;apply:identity_is.
Qed.

Lemma order_leT a b c: a <=O b -> b <=O c -> a <=O c.
Proof.
move =>[oa ob [f [x [xsb is1]]]] [_ oc [g [y [ysc is2]]]].
move: (iorder_osr ob xsb) =>[or2 sr2].
move: (iorder_osr oc ysc) =>[or3 sr3].
move:is1 =>[_ _ [bf sf tf] fiso ]; rewrite sr2 in tf.
move:is2 =>[_ _ [[[fg ig][_ sgg]] sg tg] giso ]; rewrite sr3 in tg.
have sxg: sub x (source g) by ue.
have ff: function f by fct_tac.
move:(@fun_image_Starget1 g fg x); rewrite tg; set z:= Vfs g x => zy.
move:(sub_trans zy ysc) => zsc.
move:(iorder_osr oc zsc) =>[or4 /esym sr4].
pose h  :=  (fun t => Vf g (Vf f t)).
have ax: lf_axiom h (substrate a) z.
  move => t tsx /=; apply/(Vf_image_P fg sxg); exists (Vf f t) => //; Wtac.
split => //; exists (Lf h (substrate a) z) , z; split => //; split=> //.
  hnf; saw; apply: lf_bijective.
  - done.
  - hnf; rewrite - sf; move => u v usr vsr ee.
    apply:(proj2(proj1 bf) _ _ usr vsr); apply: ig => //; apply: sxg; Wtac.
  - move => t /(Vf_image_P  fg sxg) [u ux ->].
    move:(proj2(proj2 bf)); rewrite tf => hh; move:(hh u ux); rewrite sf.
    by move =>[v vv ->]; exists v.
hnf; aw; move => u v usr vsr; rewrite !LfV //.
move:(ax _ usr)(ax _ vsr) => uz vz.
rewrite - sf in usr vsr.
apply: (iff_trans(fiso u v usr vsr)).
have fux: inc (Vf f u) x by Wtac.
have fvx: inc (Vf f v) x by Wtac.
move:(sxg _ fux) (sxg _ fvx) => fus fvs.
apply:(iff_trans (iff_trans (iorder_gle0P b fux fvx) (giso _ _  fus fvs))).
apply: (iff_trans (iorder_gle0P c (zy _ uz) (zy _  vz))).
exact (iff_sym (iorder_gle0P c uz vz)).
Qed.

Lemma order_le_compatible r r' r1 r1':
  r \Is r1 -> r' \Is r1' -> (r <=O r' <-> r1 <=O r1').
Proof.
move: r r' r1 r1'.
suff: forall r1 r2 r3 r4, r1 \Is r3 -> r2 \Is r4 -> r1 <=O r2 -> r3 <=O r4.
  by move=> aux r1 r2 r3 r4 p1 p2; split;apply: aux=>//; apply: orderIS.
move => r1 r2 r3 r4 /orderIS [f [o3 _ [[injf srf] sf tf] oif]].
move=> [g [_ o4 [[ig srg] sg tg] oig]].
move=> [o1 o2 [h [X [sX [_ _ [[ih srh] sh th] oih]]]]].
split => //.
set Y:= Vfs g X.
have sY: sub Y (substrate r4) by rewrite -tg; apply:fun_image_Starget1; fct_tac.
move: (proj1 srf) (proj1 srg) (proj1 srh) => ff fg fh.
have sX': sub X (source g) by ue.
have Yp1: forall x, inc x X -> inc (Vf g x) Y.
  move=> x xX; apply /(Vf_image_P fg sX'); ex_tac.
have Yp2: forall y, inc y Y -> exists2 x, inc x X & y = Vf g x. 
  by move=> y; move/(Vf_image_P fg sX'). 
move: th; rewrite iorder_sr // => th.
pose k x := Vf g (Vf h (Vf f x)).
have ta1: forall x, inc x (substrate r3) -> inc (k x) Y.
  rewrite - sf => t ts; apply: Yp1;Wtac; rewrite sh -tf; Wtac.
exists (Lf k (substrate r3) Y), Y; split => //.
have aux: bijection (Lf k (substrate r3) Y).
  apply: lf_bijective => //.
    rewrite - sf => u v us vs eq.
    move: (Vf_target ff us) (Vf_target ff vs); rewrite tf - sh =>  Wt1 Wt2.
    move: (Vf_target fh Wt1)(Vf_target fh Wt2); rewrite th; aw => Wt3 Wt4.
    move: (proj2 ig);rewrite sg => bi.
    move: (bi _ _ (sX _ Wt3) (sX _ Wt4) eq) => eq1.
    move: ((proj2 ih)  _ _ Wt1 Wt2 eq1) => eq2.
    by apply: (proj2 injf).
  move=> t tY; move: (Yp2 _ tY) => [x xX ->].
  rewrite - th in xX; move: ((proj2 srh) _  xX)=> [v vsf ->].
  rewrite sh - tf in vsf; move: ((proj2 srf) _ vsf)=> [w wsc ->].
  rewrite - sf; ex_tac.
move: (iorder_osr o4 sY) => [or4 sr4].
split; [exact | exact|  by rewrite sr4 /bijection_prop; aw | ].
hnf; aw; move=> u v us vs; rewrite !LfV //.
rewrite - sf in us vs; apply: (iff_trans (oif _ _ us vs)).
move: (Vf_target ff us) (Vf_target ff vs); rewrite tf - sh => Wt1 Wt2.
move: (Vf_target fh Wt1)(Vf_target fh Wt2); rewrite th => Vt1 Vt2.
move: (sX' _ Vt1) (sX' _ Vt2) => U1 U2; move: (Yp1 _ Vt1)(Yp1 _ Vt2) => X1 X2.
apply: (iff_trans (oih _ _ Wt1 Wt2)).
apply: (iff_trans(iorder_gle0P r2 Vt1 Vt2)).
apply: (iff_trans (oig  _ _ U1 U2)); symmetry; exact: iorder_gle0P. 
Qed.



(** We say  [r <= r'] if there is a order morphism; this is the same as
 saying that there is an isomorphism onto a subset of [r']  *)

Lemma order_le_alt r r':
  order r -> order r' -> (exists f, order_morphism f r r') ->
  r <=O r'.
Proof.
move => or or' [f om]; split => //.
move: om (order_morphism_fi om) => [oa oc [ff sf tf] isof] injf.
move: (restriction_to_imageE ff); set g := restriction_to_image f => eq.
have Xs: sub (target g) (substrate r').
  by move => t; rewrite - tf eq/restriction1; aw; apply:Imf_Starget.
move:(iorder_osr or' Xs)=> [or1 sr1].
have bg: bijection g by apply:restriction_to_image_fb.
have ss: source f = source g by rewrite eq /restriction1; aw.
have aux: forall x, inc x (source g) -> Vf g x = Vf f x.
  move => x xsf; rewrite eq restriction1_V //; ue.
exists g, (target g); split => //; split => //; first by split => //; ue.
move => x y xsg ysg.
apply: (iff_trans (_: gle r x y <->  (gle r' (Vf g x) (Vf g y)))).
  by rewrite (aux _ xsg) (aux _ ysg); apply: isof; rewrite ss.
split => pa; first by apply/iorder_gle0P => //; Wtac; apply: bij_function.
exact: (iorder_gle1 pa).
Qed.

Definition ordinal_leD1 r r' :=
  [/\ ordinalp r, ordinalp r' & (ordinal_o r) <=O (ordinal_o r')].
Definition ordinal_ltD1 r r' :=  ordinal_leD1 r r' /\ r <> r'.

Lemma order_le_compatible1 r r':
  worder r -> worder r' -> 
  (r <=O r' <-> ordinal_leD1 (ordinal r) (ordinal r')).
Proof.
move=> wo1 wo2. 
move: (ordinal_o_is wo1)(ordinal_o_is wo2) => oi1 oi2.
move: (OS_ordinal wo1)(OS_ordinal wo2) => o1 o2.
by apply: (iff_trans (order_le_compatible oi1 oi2));  split => //; case.
Qed.

Lemma ordinal_le_P x x': 
   ordinal_leD1 x x' <->  
   [/\ ordinalp x, ordinalp x' &
     exists f S, 
      segmentp (ordinal_o x') S /\ 
      order_isomorphism f (ordinal_o x) (induced_order (ordinal_o x') S)].
Proof.
split.
  move=> [or or' [otr otr' [f [t [sx iso]]]]];split => //.
  move: (isomorphism_worder_sub (ordinal_o_wor or') sx) =>[].
  set g := iso_seg_fun _ _ => sw isg; exists (g \cof ), (target g); split => //.
  exact: (compose_order_is iso isg).
move=> [or or' [f [t [[sx sxp] oi]]]]; split => //; split; fprops.
by exists f, t. 
Qed.

Lemma ordinal_le_P1 x x':
   ordinal_leD1 x x' <->  
   [/\ ordinalp x, ordinalp x' &
     exists2 f, segmentp (ordinal_o x') (Imf f) &
         order_morphism f (ordinal_o x)(ordinal_o x')].
Proof.
split; last first.
  move=> [or or' [f _ mf]]; split => //.
  move:(proj1 (ordinal_o_wor or)) (proj1 (ordinal_o_wor or')) => o1 o2.
  by apply /(order_le_alt o1 o2); exists f.
move /ordinal_le_P => [or or' [f [t [sx isof]]]]; split => //.
move:(proj1 (ordinal_o_wor or)) (proj1 (ordinal_o_wor or')) => o1 o2.
have sxs: sub t (substrate (ordinal_o x')) by apply: sub_segment1.
move: sx;case: (isomorphism_to_morphism o1 o2 sxs isof) => h <-.
by set g := Lf _ _ _; exists g.
Qed.

Lemma ordinal_lt_P1 x x': 
   ordinal_ltD1 x x' <-> 
   [/\ ordinalp x, ordinalp x' &
     exists f y,
        [/\ inc y x',
        Imf f = segment (ordinal_o x') y 
        & order_morphism f (ordinal_o x) (ordinal_o x')]].
Proof.
split.
  move => [] /ordinal_le_P1 [or or' [f srf om]] nrr'.
  case: (well_ordered_segment (ordinal_o_wor or') srf). 
    move => rgf;case: nrr'; apply: ordinal_o_isu => //.
    have injf:= (order_morphism_fi om).
    have [o1 o2 [ff sf tf] mf] := om.
    exists f; split => //; split => //.
    split => //;apply: surjective_pr1; [fct_tac |rewrite tf rgf //].
  move=> [t xsr rgf].
  split => //; exists f, t; split => //.
  by rewrite - (ordinal_o_sr x').
move=> [or or' [f [t [xsr rgf om]]]].
have wodr := (ordinal_o_wor or').
have odr := proj1 wodr.
have p1: segmentp (ordinal_o x') (Imf f).
  by rewrite rgf;apply: segment_segment =>//; rewrite ordinal_o_sr //.
  split; first by apply /ordinal_le_P1 => //; split => //;exists f. 
move=> rr'; rewrite rr' in  om.
move: (unique_isomorphism_onto_segment wodr p1 om); rewrite ordinal_o_sr => idf.
by case:(@not_in_segment (ordinal_o x') t); rewrite - rgf idf imf_ident.
Qed.

Lemma ordinal_lt_P x x': 
   ordinal_ltD1 x x' <-> 
   [/\ ordinalp x, ordinalp x' &
     exists f y', 
        inc y' x' /\
      order_isomorphism f (ordinal_o x) 
       (induced_order (ordinal_o x') (segment (ordinal_o x') y') )].
Proof.
split; last first.
  move => [or or' [f [y [sx isof]]]]; apply /ordinal_lt_P1; split => //.
  move:(proj1 (ordinal_o_wor or)) (proj1 (ordinal_o_wor or')) => o1 o2.
  set t := segment (ordinal_o x') y.
  have sxs: sub t (substrate (ordinal_o x')) by apply: sub_segment.
  case: (isomorphism_to_morphism o1 o2 sxs isof).
  by set g := Lf _ _ _; exists g, y.
move /ordinal_lt_P1.
set r := (ordinal_o x); set r':= (ordinal_o x').
move=> [or or' [f [y [pa pb pc]]]]; split => //.
move: pc (order_morphism_fi pc) => [oa oc [ff sf tf] isof] injf.
move: (restriction_to_imageE ff) => eq.
set g := restriction_to_image f.
have tg : target g =  segment r' y.
  rewrite /g eq /restriction1; aw; trivial;rewrite - pb - ImfE //.
have Xs: sub (target g) (substrate r') by rewrite tg; apply: sub_segment.
have [or1 sr1 ] := (iorder_osr  oc Xs).
move: (restriction_to_image_fb injf) => bg; move: (proj1(proj1 bg)) => fg.
have ss: source f = source g by rewrite /g eq /restriction1; aw.
have aux: forall x, inc x (source g) -> Vf g x = Vf f x.
  move => t xsf; rewrite /g eq restriction1_V //; ue.
exists g, y; rewrite - tg;split => //; split => //;first by split => //; ue.
move => u v usg vsg; move: (usg)(vsg); rewrite - ss => usf vsf.
apply:(iff_trans (isof _ _ usf vsf)); rewrite -  (aux _ usg) - (aux _ vsg).
split => pd; [by apply/iorder_gle0P => //; Wtac | exact: (iorder_gle1 pd) ].
Qed.

Lemma ordinal_lt_pr2 a b:
  worder b -> ordinal_ltD1 a (ordinal b) ->
  exists f x,
    [/\ inc x (substrate b),
     Imf f = segment b x & order_morphism f (ordinal_o a) b].
Proof.
move=> ob /ordinal_lt_P1 [oa op [f [x [xsp rgx om]]]].
have [g oig]: order_isomorphic (ordinal_o (ordinal b)) b.
  by apply: orderIS; apply: (ordinal_o_is ob). 
move: om (oig) => [o1 o2 [ff sf tf] pf][_ o4 [[gi gs] sg tg] pg].
have cfg:  g \coP f by split => //; try fct_tac; ue.
rewrite  ! ordinal_o_sr in sf tf sg.
have p0: function (g \co f) by fct_tac. 
have p3: order_morphism (g \co f) (ordinal_o a) b.
  split=> //; first by saw; rewrite ordinal_o_sr.
  hnf; aw; move=> u v asf bsf; rewrite ! compfV //.
  apply: (iff_trans (pf _ _ asf bsf)); apply/ pg; rewrite sg - tf; Wtac.
set y:= (Vf g x).
have p1: inc y  (substrate b) by rewrite /y;Wtac; fct_tac.
exists (g \co f), y; split => //.
set_extens u.  
  move /(Imf_P p0)=> [v vsf ->].
  rewrite compf_s in vsf.
  have /segmentP xx : inc (Vf f v) (segment (ordinal_o (ordinal b)) x).
    by rewrite -rgx; Wtac.
  by rewrite compfV //;apply /segmentP; apply (order_isomorphism_sincr oig).
move/segmentP=> buy.
have utg: inc u (target g) by rewrite tg; order_tac.
move: ((proj2 gs) _ utg) buy => [v vsg ->].
rewrite - sg in xsp.
move/(order_isomorphism_siso oig vsg xsp) => /segmentP.
rewrite -rgx; move/(Imf_P ff) => [w pa pb].
apply/(Imf_P p0); aw; ex_tac; rewrite pb; rewrite compfV //.
Qed.

Lemma ordinal_le_P0 x y:
  ordinal_leD1 x y <-> [/\ ordinalp x, ordinalp y & sub x y].
Proof.
split; last first.
  move => [ox oy sxy];split => //.
  split; fprops; rewrite ordinal_o_sr. 
  exists (identity x), x; split => //.
  have ->: induced_order (ordinal_o y) x = (ordinal_o x).
     set_extens t. 
       by move => /setI2_P [] /Zo_P [pa pb] pc; apply: Zo_i.
     move =>/ Zo_P [pa pb]; apply/setI2_P;split => //; apply: Zo_i => //.
     by apply: (setX_Slr sxy sxy).
  rewrite - {1} (ordinal_o_sr x); apply: identity_is; fprops.
move /ordinal_le_P => [ox oy [f [S [sS oi]]]]; split => //.
move: (ordinal_o_wor oy) => woy.
have [p1 p2 p3]: 
   [/\ sub S y, ordinalp S & (induced_order (ordinal_o y) S) = ordinal_o S].
  case: (well_ordered_segment woy sS).
    move ->;rewrite iorder_substrate; [ by rewrite ordinal_o_sr; split| fprops].
  move=> [u]; rewrite ordinal_o_sr => uy.
  move: (ordinal_transitive oy uy) => suy.
  rewrite ordinal_segment // => ->.
  split => //; first exact:(Os_ordinal oy uy). 
  set_extens t; first by move/setI2_P => [] /Zo_P [pa pb] pc;apply /Zo_P; split.
  move/Zo_P =>[pa pb]; apply/setI2_i => //.
  by apply: Zo_i => //;apply:(setX_Sll suy). 
rewrite p3 in oi.
by rewrite (proj1 (ordinal_isomorphism_unique ox p2 oi)).
Qed.

(** [ordinal_leD1 E E'] simplifies to [sub E E'] when [E] and [E'] are ordinals*) 

Definition ordinal_le x y :=
  [/\ ordinalp x, ordinalp y & sub x y].
Definition ordinal_lt x y := ordinal_le x y /\ x <> y.
Definition ole_on x := graph_on ordinal_le x.

Notation "x <=o y" := (ordinal_le x y) (at level 60).
Notation "x <o y" := (ordinal_lt x y) (at level 60).


(** We study here [ordinal_le]; it is a well-ordering *)

Lemma oltP0 x y:
  x <o y <-> [/\ ordinalp x, ordinalp y & inc x y].
Proof.
split.
   by move=> [[ox oy sxy] nxy]; split => //; case: (ordinal_sub ox oy sxy).
by move=> [ox oy xy]; move: (ordinal_sub2 oy xy) => [pa pb].
Qed.

Lemma olt_i x y: x <o y -> inc x y.
Proof. by case/oltP0. Qed.

Lemma oltP a: ordinalp a -> forall x, (x <o a <-> inc x a).
Proof.
move=> oa x; split; first by apply:olt_i.
move => xa; apply/oltP0; split => //; exact:(Os_ordinal oa xa).
Qed.

Lemma oleP a: ordinalp a ->
  forall x, (x <=o a <-> inc x (osucc a)).
Proof.
move=> oa x; split.
 by move=> [pa _ pc]; apply /ordinal_sub4P.
move => aux; move: (ordinal_sub3 oa aux) => xa; split => //.
apply: (Os_ordinal (OS_succ oa) aux).
Qed.

Lemma least_ordinal0 E (x:= intersection E): ordinal_set E -> nonempty E ->
  [/\ ordinalp x, inc x E & forall y, inc y E -> x <=o y].
Proof.
move => sa sb.
have xe:= (ordinal_setI sb sa).
have ox:=(sa _ xe).
split => // y yE;split;[ exact | exact (sa _ yE)| exact:(setI_s1 yE)].
Qed.

Theorem wordering_ole: worder_r ordinal_le.
Proof.
split; first split. 
  - move=> x y z [Kx Ky xy][_ Kz yz].
    by split => //; apply: sub_trans yz.
  - move=> x y [Kx Ky xy][_ _ yx].
    by apply: extensionality.
  - by move=> x y [ox oy _]; split => //;split.
move=> x ale nex.
have alo: ordinal_set x by move=> a /ale [h _].
move: (least_ordinal0 alo nex) => [ha hb hc].
exists (intersection x); hnf; rewrite (graph_on_sr ale); split=> // a ax.
by apply /graph_on_P1; split => //; apply:hc.
Qed.

Lemma wordering_ole_pr x:
  ordinal_set x -> worder_on (ole_on x) x.
Proof.
move => osx.
by apply: wordering_pr; [apply: wordering_ole |  move => a /osx ox; split].
Qed.

Lemma ole_order_r: order_r ordinal_le.
Proof. exact: (proj1 wordering_ole). Qed.

Lemma oleR x: ordinalp x -> x <=o x.
Proof. by move=> or; split.  Qed.

Hint Resolve oleR: fprops.

Lemma oleT y x z: x <=o y -> y <=o z -> x <=o z.
Proof. move: ole_order_r => [p1 p2 _]; apply: p1. Qed.

Lemma oleA x y: x <=o y -> y <=o x ->  x = y.
Proof. move: ole_order_r => [p1 p2 _]; apply: p2. Qed.

Lemma ole_eqVlt a b : a <=o b -> (a = b \/ a <o b).
Proof.
move => h1; case: (equal_or_not a b) => h2; [by left | by right ].
Qed.

Lemma oleNgt x y: x <=o y -> ~(y <o x).
Proof. by move=> ole [olt one]; case: one; apply: oleA. Qed.

Lemma oltNge x y: x <o y -> ~ (y <=o x).
Proof. move => pa pb; exact:(oleNgt pb pa). Qed.

Lemma olt_leT a b c: a <o b -> b <=o c -> a <o c.
Proof. 
move=> [ab nab] bc; split; first by apply: (oleT ab bc). 
by dneg ac;  rewrite -ac in bc; apply: oleA.
Qed.

Lemma ole_ltT b a c: a <=o b -> b <o c -> a <o c.
Proof. 
move=> ab [bc nbc]; split; first by apply: (oleT ab bc). 
by dneg ca; rewrite ca in ab; apply: oleA.
Qed.

Lemma olt_ltT b a c: a <o b -> b <o c -> a <o c.
Proof. by move=>  [ab _] bc; apply: (ole_ltT ab bc). Qed.

Lemma oleT_ell a b:
 ordinalp a -> ordinalp b -> [\/ a = b, a <o b | b <o a].
Proof.
move=> oa ob. 
case: (ordinal_inA oa ob) =>  ha.
- by constructor 2; apply/oltP. 
- by constructor 3; apply/oltP. 
- by constructor 1.
Qed.

Lemma oleT_el a b: 
  ordinalp a -> ordinalp b -> a <=o b \/ b <o a.
Proof.
move=> oa ob; case:(oleT_ell oa ob).
- move ->; left; fprops.
- by move => [h _]; left.
- by right.
Qed.


Lemma oleT_ee a b: 
  ordinalp a -> ordinalp b -> a <=o b \/ b <=o a.
Proof.
by move=> oa ob; case: (oleT_el oa ob); [by left | move => [h _]; right ].
Qed.

Lemma oleT_si a b: 
  ordinalp a -> ordinalp b -> (sub a b \/ inc b a).
Proof.
move=> oa ob; case: (oleT_el oa ob); first by move => [_ _]; left.
by move/olt_i; right.
Qed. 
  
(** Min and max *)
Definition omax:= Gmax ordinal_le.
Definition omin:= Gmin ordinal_le.

Lemma OS_omax x y: ordinalp x -> ordinalp y -> ordinalp (omax x y).
Proof. by apply:Gmax_S. Qed.

Lemma SS_omin x y: ordinalp x -> ordinalp y -> ordinalp (omin x y).
Proof. by apply:Gmin_S. Qed.

Lemma omax_xy x y: x <=o y -> omax x y = y.
Proof. by apply:Gmax_xy. Qed.

Lemma omax_yx x y: y <=o x -> omax x y = x.
Proof. apply: (Gmax_yx oleA). Qed.
 
Lemma omin_xy x y: x <=o y -> omin x y = x.
Proof. by apply: Gmin_xy. Qed.

Lemma omin_yx x y: y <=o x -> omin x y = y.
Proof. apply: (Gmin_yx oleA). Qed.  

Lemma omaxC x y: ordinalp x -> ordinalp y -> omax x y = omax y x.
Proof. apply: (GmaxC oleA oleT_ee). Qed.

Lemma ominC x y: ordinalp x -> ordinalp y -> omin x y = omin y x.
Proof. apply: (GminC oleA oleT_ee). Qed.

Lemma omax_p1 x y: ordinalp x -> ordinalp y ->
   x <=o (omax x y) /\ y <=o (omax x y).
Proof. apply:(Gmax_p1 oleA oleR oleT_ee). Qed.

Lemma omin_p1 x y:  ordinalp x -> ordinalp y ->
   (omin x y)  <=o x /\ (omin x y) <=o y.
Proof. apply:(Gmin_p1 oleA oleR oleT_ee). Qed.


Lemma omax_p0 x y z: x <=o z -> y <=o z -> (omax x y) <=o z.
Proof. apply:Gmax_p0. Qed.

Lemma omin_p0 x y z: z <=o x -> z <=o y -> z <=o (omin x y).
Proof.  apply:Gmin_p0. Qed.

Lemma omaxA x y z: ordinalp x -> ordinalp y -> ordinalp z -> 
    omax x (omax y z) = omax (omax x y) z.
Proof. apply: (GmaxA  oleA oleR oleT oleT_ee). Qed.

Lemma ominA x y z: ordinalp x -> ordinalp y -> ordinalp z -> 
    omin x (omin y z) = omin (omin x y) z.
Proof. apply: (GminA oleA oleR oleT oleT_ee). Qed.
 
Lemma ominmax x y z: 
  ordinalp x -> ordinalp y -> ordinalp z ->
  omin x (omax y z) = omax (omin x y) (omin x z).
Proof. apply: (Gminmax oleA oleR oleT oleT_ee). Qed.

Lemma omaxmin x y z: 
  ordinalp x -> ordinalp y -> ordinalp z ->
  omax x (omin y z) = omin (omax x y) (omax x z).
Proof.  apply: (Gmaxmin oleA oleR oleT oleT_ee). Qed.

(** more least ordinal *)


Lemma order_cp1_total x y: total_order x -> order y -> sub x y ->
  (sub (substrate x) (substrate y) /\ x = (induced_order y (substrate x))).
Proof.
move => to1 o2 xy.
move: (proj1 to1) => o1.
have aa: sub (substrate x) (substrate y).
  move => t tsa; apply /(order_reflexivityP o2); apply: xy.
  by apply /(order_reflexivityP o1).
have [sa sb]:=(iorder_osr o2 aa).
split => //; apply: extensionality.
   move => t tx; apply /setI2_P; split; fprops.
   apply:sub_graph_coarse_substrate; fprops.
move => t /setI2_P [ty /setX_P [pa pb pc]]; rewrite - pa.
case: (proj2 to1 _ _ pb pc) => // h2.
rewrite -pa in ty.
move: (order_antisymmetry o2 (xy _ h2) ty) => h3; by move: h2; rewrite h3.
Qed.


Lemma order_cp1 x y: worder x -> worder y -> sub x y ->
  (sub (substrate x) (substrate y) /\ x = (induced_order y (substrate x))).
Proof.
by move => /worder_total wo1 /proj1 wo2 xy; apply: (order_cp1_total).
Qed.

Lemma order_cp2 x y: worder x -> worder y -> sub x y -> ordinal x <=o ordinal y.
Proof.
move => wo1 wo2 xy.
have [pa pb]:= (order_cp1 wo1 wo2 xy).
suff: x <=O y by move /(order_le_compatible1 wo1 wo2) /ordinal_le_P0.
split; fprops; exists (identity (substrate x)), (substrate x); split => //.
rewrite -pb; apply: identity_is; fprops.
Qed.

Lemma order_cp3 x y: worder x -> worder y -> 
   ssub x y -> (segmentp y (substrate x)) -> ordinal x <o ordinal y.
Proof.  
move => wo1 wo2 [xy xny] sp.
split; [ by apply: order_cp2 | move => so ].
move: (ordinal_o_is wo2) (orderIS (ordinal_o_is wo1)); rewrite so => pa pb.
move: (order_cp1 wo1 wo2 xy) => [ss xx].
move: (orderIT pa pb) => [f]; rewrite xx => isf.
move: (isomorphism_to_morphism (proj1 wo2) (proj1 wo2) ss  isf).
set g := Lf _ _ _; move => [pc rg].
have pd: segmentp y (Imf g) by rewrite rg.
move: rg; rewrite (unique_isomorphism_onto_segment wo2 pd pc) imf_ident => srr.
by case: xny; rewrite xx - srr (iorder_substrate (proj1 wo2)).
Qed.


(** We study the properties of the least ordinal *)


Lemma least_ordinal4 x (p: property) (y := least_ordinal p x):
 ordinalp x -> p x ->
   [/\ ordinalp y, p y & (forall z, ordinalp z -> p z -> y <=o z) ].
Proof.
move=> ox px; move: (least_ordinal1 ox px) => [p1 p2 p3].
split => // t ot pt;move: (p3 _ ot pt) => zt; hnf;split => //.
Qed.

Lemma least_ordinal3 x (p: property) (y := least_ordinal (fun z => (~ p z)) x):
 ordinalp x -> ~ (p x) ->
   [/\ ordinalp y, ~(p y) & (forall z, z <o y -> p z)].
Proof.
move=> ox px. 
move: (least_ordinal4 (p:= (fun z => ~ p z)) ox px) => [p1 p2 p3].
split => // z zy.
by ex_middle npz; move: (p3 _ (proj31_1 zy) npz) => /(oltNge zy). 
Qed.

Lemma least_ordinal6 x (p:property) (y :=least_ordinal (fun z => ~ p z) x):
  ordinalp x ->
  p x \/ [/\ ordinalp y, forall z, inc z y -> p z & ~ p y].
Proof.
move => oc; case: (p_or_not_p (p x)) => np; [by left | right].
move:(least_ordinal3 oc np) => [pa pb pc]; split => // z zy. 
by apply:pc; apply/(oltP pa).
Qed.

Lemma least_ordinal2 (p:property) : 
  (forall b, ordinalp b ->  (forall x, x <o b -> p x) -> p b) ->
  forall a,  ordinalp a -> p a.
Proof.
move => H a oa.
case: (p_or_not_p (p a)) => np //.
move: (least_ordinal3 oa np).
set y := least_ordinal _ _. move => [oy npy Hy]; case: npy => //.
by apply: (H _ oy) => x /Hy lxy. 
Qed.

Lemma least_ordinal2' (p:property) : 
  (forall b, ordinalp b ->  (forall x, inc x b -> p x) -> p b) ->
  forall a,  ordinalp a -> p a.
Proof.
move => H; apply:least_ordinal2 => b ob bp; apply:(H _ ob) => x /(oltP ob).
exact: bp.
Qed.


(** [union] is the supremum of a family of ordinals, cardinals or 
the predecessor of an ordinal. We study here the supremum of ordinals *)


Notation "\oinf" := intersection (only parsing).
Notation "\osup" := union (only parsing).
Notation "\csup" := union (only parsing).

Definition ordinal_ub E x:= forall i, inc i E -> i <=o x.

Lemma OS_sup E: ordinal_set E -> ordinalp (\osup E).
Proof. 
move=> alo; apply: ordinal_pr.
  by apply: transitive_setU => y yx; apply: ordinal_transitive; apply: alo. 
move=> y /setU_P [a ya ax].
exact: (Os_ordinal (alo _ ax) ya).
Qed.

Lemma ord_sup_ub E: ordinal_set E -> ordinal_ub E (\osup E).
Proof.
by move=> Ep i iE; split; [ apply: Ep | apply: OS_sup | apply: setU_s1].
Qed.

Lemma ord_ub_sup E y: ordinalp y -> ordinal_ub E y ->
  \osup E <=o y.
Proof.
move => oy h; split => //.
  by apply:OS_sup => i /h /proj31.
by move=> i /setU_P [z iz /h [_ _]]; apply.
Qed.

(* Lemma ord_sup_prop moved top ssere11 *)
  
Lemma unbounded_non_coll (p:property):
  (forall x, ordinalp x -> exists2 y, x <=o y & p y) -> non_coll p.
Proof.
move => hp [E Ep].
set F := Zo E ordinalp.
have ose: ordinal_set F by move => x /Zo_hi. 
move:(hp _ (OS_succ (OS_sup ose))) => [y [os oy lexy] /Ep yE].
have lyx :=(lexy _ (setU1_1 (\osup F) (\osup F))).
by case :(oleNgt (ord_sup_ub ose (Zo_i yE oy))); apply/(oltP oy).
Qed.

Lemma non_collectivizing_ordinal_bis: non_coll ordinalp.
Proof.
by apply:unbounded_non_coll => x ox; move:(oleR ox)=> xx; exists x. 
Qed.


(** The empty set is the least ordinal *)

Definition ord_zero := emptyset.
Notation "\0o" := ord_zero.

Lemma OS0: ordinalp \0o.
Proof. move => y ye _ []; apply: extensionality; fprops. Qed. 

Lemma ole0x x: ordinalp x -> \0o <=o x.
Proof. move=> ox; split; fprops; apply: OS0. Qed.

Lemma ord_ne0_pos x: ordinalp x -> x <> \0o -> \0o <o x.
Proof. by move => ox xnz; split; [ apply: ole0x | apply nesym ]. Qed.

Lemma ole0 x: x <=o \0o -> x = \0o.
Proof. by move => [ _ _ /sub_set0]. Qed.

Lemma olt0 x: x <o \0o -> False.
Proof. by move=> [/ole0 pa pab]. Qed.

Lemma ord_gt_pos x y: y <o x -> \0o <o x.
Proof. move=> h; exact :(ole_ltT (ole0x (proj31_1 h)) h). Qed.


(** [osucc x] is the next ordinal after [x] *)


Lemma osucc_pr0 x (z:= osucc x): ordinalp x -> 
  x <o z /\ (forall w, x <o w -> z <=o w).
Proof.
move=> ox; move: (OS_succ ox)=> oz. 
split; first by apply/(oltP oz); fprops.
move=> w /oltP0 [_ ow xw].
split => // t /setU1_P []; last by move=> ->.
by apply: (ordinal_transitive ow).
Qed.

Lemma oltS a: ordinalp a -> a <o (osucc a).
Proof. by case /osucc_pr0. Qed.

Lemma oleS a: ordinalp a -> a <=o (osucc a).
Proof. by case/oltS. Qed. 

Lemma oltSleP a b: a <o (osucc b) <-> a <=o b.
Proof.
split.
  move /oltP0=> [p1 /OS_succr p2 p3]. 
  by split => //; apply: ordinal_sub3.
move => [p1 p2]; move/(ordinal_sub4P p1 p2) => q; apply/oltP0.
split; fprops.
Qed.

Lemma oleSltP a b: a <o b <-> (osucc a) <=o b.
Proof.
split.
  by move => h; apply :(proj2 (osucc_pr0 (proj31_1 h))).  
move => [pa pb pc]; have asa:= (pc _ (setU1_1 a a)).
apply /oltP0;split => //; exact:(Os_ordinal pb asa).
Qed.

Lemma oleSSP x y:  (osucc x <=o osucc y) <-> x <=o y.
Proof. 
split => h; last by apply /oleSltP /oltSleP.
by apply /oltSleP /oleSltP.
Qed.

Lemma oltSSP x y: (osucc x <o osucc y) <->  (x <o y).
Proof. 
split => h; last by apply /oltSleP /oleSltP. 
by apply /oleSltP /oltSleP. 
Qed.

Definition osuccp x := exists2 y, ordinalp y & x = osucc y.
Definition opred := union. 

Lemma opred_le x: ordinalp x -> opred x <=o x.
Proof.
move => ox;split; [ exact: (OS_sup (Os_ordinal ox)) | exact | ].
move => t /setU_P [y ty yx]; exact:(ordinal_transitive ox yx ty).
Qed.


Lemma succo_K y: ordinalp y -> opred (osucc y) = y.
Proof. 
move=> oy; set_extens t => ts; last by apply: (setU_i ts); fprops.
move: (setU_hi ts) => [a ta]; case /setU1_P;last by move => <-.
move => ay;exact:(ordinal_transitive oy ay ta).
Qed.

Lemma predo_K x: osuccp x -> osucc (opred x) = x.
Proof.
by move=>  [y oy xs]; rewrite xs (succo_K oy).
Qed.

Lemma osuccNpred x: osuccp x -> x = opred x -> False.
Proof.
move => [y oy yt] xv; case: (nesym (proj2 (oltS oy))).
by move: (succo_K oy); rewrite - yt - xv yt.
Qed.  

Lemma osuccVpred x: ordinalp x -> osuccp x \/ x = opred x.
Proof.
move => ox; move: (opred_le ox) => la.
case: (equal_or_not x (opred x)) => h; [ by right | left; exists (opred x) ].
   apply: (proj31 la).
apply: oleA; last by move/oleSltP: (conj la (nesym h)).
split => //; [ exact: (OS_succ (proj31 la)) | move => t tx].
by move /oltSleP: (ord_sup_ub (Os_ordinal ox) tx) => /olt_i.
Qed.

(** a limit ordinal is a non-successor; it contains zero and is stable 
by [osucc]; it is the supremum of all elements smaller than itself
 *)

Definition limit_ordinal x:= 
  [/\ ordinalp x, inc \0o x & (forall y, inc y x -> inc (osucc y) x)].

Lemma limit_nonsucc x: limit_ordinal x -> x = opred x.
Proof. 
move => [ox zx sx].
case: (osuccVpred ox) => // [] [y oy xy].
have yx: (inc y x) by rewrite xy; fprops.
by move: (sx _ yx); rewrite -xy => /(ordinal_irreflexive ox).
Qed.

Lemma limit_pos x: limit_ordinal x -> \0o <o x.
Proof. 
move=> [ox h _]; apply: ord_ne0_pos => // xz. 
by case: (@in_set0 \0o); move:h; rewrite xz.
Qed.

Lemma limit_nz x: limit_ordinal x -> x <> \0o. 
Proof. by move /limit_pos =>[_ /nesym].  Qed.

Lemma limit_ordinal_P x:
  limit_ordinal x <-> 
  (\0o <o x /\ forall t, t <o x -> osucc t <o x).
Proof.
split.
  move => lx; split; first by apply: limit_pos.
  move:lx => [ox xnz xl].
  by move => t /(oltP ox) => h; apply/(oltP ox); apply: xl.
move =>[[sa xnz] sb];move: (proj32 sa) => ox; split => //.
  exact: (olt_i (ord_ne0_pos ox (nesym xnz))).
by move => t /(oltP ox) h; apply/(oltP ox); apply: sb.
Qed.

Lemma limit_ordinal_P0 x: ordinalp x ->
  ((limit_ordinal x) <-> (nonempty x /\ x = opred x)).
Proof.
move=> ox; split. 
  move => lx; move:(limit_nonsucc lx) => sa; split => //.
  by move: (proj32 lx) => zx; exists emptyset.
move => [/nonemptyP nex ww]. apply/limit_ordinal_P; split.
  exact: (ord_ne0_pos ox nex).
move => t /oleSltP h; split => // h'.
have osx: osuccp x  by exists t=> //; apply: OS_succr; ue.
exact: (osuccNpred osx ww). 
Qed.

Lemma ordinal_limA x: ordinalp x ->
  [\/ x = \0o, osuccp x | limit_ordinal x].
Proof.
move=> ox.
case: (emptyset_dichot x); first by constructor 1.
move=> nex.
case: (osuccVpred ox); first by constructor 2.
by move=> xu; constructor 3; apply /(limit_ordinal_P0 ox). 
Qed.

(** If from two equipotent sets we remove an element, we get equipotent sets*)

Section SuccProp.
Variables (x y a b: Set).
Hypotheses (nax:  ~ inc a x) (nby: ~ inc b y).


(** this says that a superset of an infinite set is infinite *)

Lemma sub_inf_aux:
  sub x y -> x \Eq (x +s1 a) -> y \Eq (y +s1 b).
Proof.
move=> sxy /EqS [f [[[ff injf] sjf] sf tf]].
have nbx: ~ inc b x by dneg bx; apply: sxy.
apply:EqS.
have Asf: inc a (source f) by rewrite sf; fprops.
have wafx: inc (Vf f a) x by Wtac.
set g := fun z => Yo (inc z x) (Vf f z) (Yo (z = b) (Vf f a) z).
have Byp: forall t, inc t y -> t <> b by move=> t ty tB; case: nby; ue.
have pa: lf_axiom g (y +s1 b) y.
  move=> t /setU1_P; rewrite /g; case.
    move=> ty; Ytac tx; first by apply: sxy; Wtac; rewrite sf; fprops.
    by move: (Byp _  ty) => aux; Ytac0. 
  by move => ->; Ytac0; Ytac0; apply: sxy.
have pb: forall u v, inc u (y +s1 b) -> inc v (y +s1 b) -> g u = g v -> u = v.
  move=> u v; rewrite /g; case /setU1_P => uy /setU1_P aux; last first.
    rewrite uy; Ytac0; Ytac0; Ytac vx.
      have vsf: inc v (source f) by rewrite sf; fprops.
      by move=> h; rewrite -(injf _ _ Asf vsf h) in vx.
    case:aux => vy //.
    by move: (Byp _ vy) => aux;Ytac0 => h; rewrite -h in vx.
  Ytac ux.
    Ytac vx; first by apply: injf; rewrite sf; fprops.
    case: aux => vy.
      move: (Byp _  vy) => aux; Ytac0=> h; case: vx; rewrite -h -tf.
      Wtac; rewrite sf; fprops.
    Ytac0 => aux.
    have usf: inc u (source f) by rewrite sf; fprops.
    by rewrite (injf _ _ usf Asf aux) in ux.
  have uB: u <> b by move => ub; case: nby; ue.
  Ytac0; Ytac vx.
      move=> h; rewrite h in ux; case: ux; rewrite -tf.
      Wtac; rewrite sf; fprops.
  case: aux => vy; [move: (Byp _ vy) => aux |]; Ytac0 => //.
  move=> h;case: ux; ue. 
exists (Lf g (y +s1 b) y);  saw; apply: lf_bijective => // t ty.
case: (inc_or_not t x) => tx.
  rewrite -tf in tx; move: ((proj2 sjf) _ tx)=> [z zsf wz].
  move: zsf; rewrite sf;case /setU1_P => zx.
    exists z; first by apply /setU1_P; left; apply: sxy.
    by rewrite /g; Ytac0.
  by exists b; fprops; rewrite /g; Ytac0; Ytac0; rewrite - zx wz.
by move: (Byp _ ty) => aux;exists t; fprops;rewrite /g; Ytac0; Ytac0. 
Qed.


Lemma succ_inf_aux_p1: x \Eq y -> (x +s1 a) \Eq (y +s1 b).
Proof.
move=> [f [ [[ff injf] srjf] sf tf]].
have sjt: surjection (extension f a b) by apply: extension_fs =>//;ue.
have st: source (extension f a b) = x +s1 a by rewrite /extension; aw;ue.
have tt: target (extension f a b) = y +s1 b by rewrite /extension; aw;ue.
have asf: ~ inc a (source f) by ue.
exists (extension f a b); split => //.
 split => //; split; first by fct_tac.
 rewrite st; move=> u v; case /setU1_P=> us; case /setU1_P => vs.
 + rewrite ! extension_Vf_in //; try ue; apply: injf; ue.
 + rewrite (extension_Vf_in _ ff asf); last by ue.
   rewrite vs (extension_Vf_out _ ff asf);move =>h;case:nby;rewrite -h; Wtac.
 + rewrite us(extension_Vf_out _ ff asf)(extension_Vf_in _ ff asf);last by ue.
   move =>h; case: nby; rewrite h; Wtac.
 + rewrite us vs !extension_Vf_out //.  
Qed.

Lemma succ_inf_aux_p2: ((x +s1 a) \Eq (y +s1 b) -> x \Eq y).
Proof.
move =>[f [bf sf tf]].
move:(bf) =>[[ff injf] [_ sjf]].
have yt: inc b (target f) by rewrite tf; fprops.
move: (inverse_V bf yt) (inverse_Vis bf yt).
set a' := Vf (inverse_fun f) b => Wa asf'.
exists (Lf (fun z => Yo (z = a') (Vf f a) (Vf f z)) x y); saw.  
have asf: inc a (source f) by rewrite sf; fprops.
have sxsf: sub x (source f) by rewrite sf => t; fprops.
apply: lf_bijective.
+ move=> z bx /=; Ytac ba.
    move: (Vf_target ff asf); rewrite tf.
    case /setU1_P => // h; rewrite - h in Wa; move: (injf _ _ asf' asf Wa). 
    by move=> ab; case: nax; rewrite - ab - ba.
  have bsf: inc z (source f) by rewrite sf; fprops.
  move: (Vf_target ff bsf); rewrite  tf.
  case /setU1_P => // h; rewrite -h in Wa; move: (injf _ _ asf' bsf Wa).     
  by move=> ab; case: ba. 
+ move=> u v ux vx; Ytac ua.
    Ytac va; first by rewrite ua va.
    move=> WW; move: (injf _ _ asf (sxsf _ vx) WW) => aux.
    by rewrite -aux in vx.
  Ytac va; last by move=> ww;apply:  (injf _ _ (sxsf _ ux) (sxsf _ vx) ww).
  move=> WW;move: (injf _ _ (sxsf _ ux) asf WW) => aux.
  by case: nax; rewrite -aux.
+ move=> z zt.  
  have ztf: (inc z (target f)) by rewrite tf; fprops.
  case: (equal_or_not z (Vf f a)) => zW.
    rewrite zW; exists a' => //; last by Ytac0. 
    move: asf'; rewrite sf; case /setU1_P => //.
    by move=> ax;move: zt; rewrite zW;  rewrite -{1} ax  Wa.
  move: (sjf _  ztf) => [b' bsf Wb].
  case: (equal_or_not b' a') => ba.
    by move: nby; rewrite - Wa - ba - Wb.
  exists b'; last by Ytac0.
  move: bsf; rewrite sf; case /setU1_P => // bx.
  by case: zW; rewrite Wb bx.
Qed.

End SuccProp.

Lemma succ_inf_aux_ord x y: ordinalp x -> ordinalp y ->
  ((osucc x) \Eq (osucc y) <-> x \Eq y).
Proof.
move=> /ordinal_irreflexive xa /ordinal_irreflexive yb; split.
   move => fp; exact:(succ_inf_aux_p2 xa yb fp).
move => fp; exact:(succ_inf_aux_p1 xa yb fp).
Qed.

(* a definition of omega *)
Section Infinite1.

Definition z_infinite E := inc \0o E /\ forall x, inc x E -> inc (osucc x) E.
Variable E0: Set.
Hypothesis HE: z_infinite E0.

Definition z_omega := intersection (Zo (\Po E0) z_infinite).

Lemma limit_z_infinite x: limit_ordinal x -> z_infinite x.
Proof. by case. Qed.


Lemma z_omega_prop :
  z_infinite z_omega /\ forall E, z_infinite E -> sub z_omega E.
Proof.
have nez:  nonempty (Zo (\Po E0) z_infinite).
  by exists E0; apply:Zo_i => //; apply/setP_P.
have Ho: z_infinite z_omega.
   split; first by apply/(setI_P nez) => i /Zo_P [ _ []].
   move => x xo;apply/(setI_P nez) => i iZ; move:(iZ)=> /Zo_P [ _ [_]]; apply.
   exact: (setI_hi xo iZ).
split => // E iE; apply: sub_trans  (@setI2_1 E E0).
apply: setI_s1; apply:Zo_i; first by apply/setP_P; apply:setI2_2.
move: HE iE =>[pa pb][pc pd].
split. fprops. move => t /setI2_P [/pd qd /pb qb]; fprops.
Qed.

Lemma z_omega_rec (p: property):
  p \0o ->  (forall x, inc x z_omega -> p x -> p (osucc x)) ->
    forall x, inc x z_omega -> p x.
Proof.
move => P0 Hrec.
set E := Zo z_omega p.
move: z_omega_prop => [[qa qb] qc].
have /qc s: z_infinite E.
  split; [apply:Zo_i | move => x /Zo_P [ ra rb]; apply: Zo_i]; fprops.
by move => x /s/Zo_hi.
Qed.

Lemma z_omega_ordinal: ordinalp z_omega. 
Proof.
apply: ordinal_pr.
  apply:z_omega_rec; first by move => t/in_set0.
  by move => x pa pb; apply: setU1_sub.
by apply:(z_omega_rec OS0) => x _ /OS_succ.
Qed.

Lemma z_omega_limit:
  limit_ordinal z_omega /\ forall z, limit_ordinal z -> z_omega <=o z. 
Proof.
move: z_omega_prop  z_omega_ordinal =>[ [qa qb] qc] oo.
split; first by split.
by move => y [pa pb pc]; split => //; apply: qc. 
Qed.

Lemma z_omega_infinite (f := Lf osucc z_omega z_omega):
  injection_prop f z_omega z_omega /\ Imf f = z_omega -s1 \0o.
Proof.
move: z_omega_prop  z_omega_ordinal =>[ [qa qb] qc] oo.
have H: injection_prop f z_omega z_omega.
  rewrite /f; saw; apply: lf_injective => //.
  by move => u v ua uv; apply: osucc_inj; apply: (Os_ordinal oo).
move: (H) => [[ff injf] sf tf].
have/qc ii: z_infinite ((Imf f) +s1 \0o).
  split; fprops => x /setU1_P hh; apply: setU1_r;apply/(Imf_P ff).
  rewrite sf /f; case: hh; last by move ->; exists \0o => //;rewrite LfV.
  by move/(Imf_Starget  ff); rewrite tf => xo; ex_tac; rewrite LfV.
split => //; set_extens t.
  move/(Imf_P ff) =>[u usf ->]; apply/setC1_P; rewrite /f; rewrite sf in usf.
  rewrite LfV //; split; fprops; rewrite/ord_zero => h; empty_tac1 u.
by move => /setC1_P [/ii /setU1_P to tnz]; case: to. 
Qed.


Lemma z_omega_infinite2: z_omega \Eq (osucc z_omega).
Proof.
move:  z_omega_infinite; set f := Lf _ _ _; move => [[fi sf tf] pb].
move: (restriction_to_image_fb fi) => bf.
move:(ordinal_irreflexive (z_omega_ordinal)) z_omega_prop => ha /proj1/proj1 hd.
have hb: ~ inc \0o (Imf f) by rewrite pb => /setC1_P[].
move: (succ_inf_aux_p1 ha hb). rewrite {2} pb (setC1_K hd) => h.
apply: EqS; apply: h.
exists (restriction_to_image f).
by split => //; rewrite /restriction_to_image/restriction2; aw.
Qed.

End Infinite1.


(** We say that [x] is infinite if equipotent to its successor; 
finite otherwise; note that [ordinalp x] is missing in the definition 
of infinite  *)
Definition infinite_o u := u \Eq (osucc u).
Definition finite_o u := ordinalp u /\ ~ (infinite_o u).

Lemma OIS_in_inf x y: ordinalp y ->
  inc x y -> infinite_o x -> infinite_o y.
Proof.
move =>  oy xy.
move: (ordinal_irreflexive (Os_ordinal oy xy)) => ha.
move:(ordinal_irreflexive oy) (ordinal_transitive oy xy) => hb hc [f xx].
have xi: x \Eq (osucc x) by exists f.
exact (sub_inf_aux ha hb hc xi).
Qed.

Lemma OIS_le_inf x y: x <=o y -> infinite_o x -> infinite_o y.
Proof.
case/ole_eqVlt; [ by move -> | move => lt].
exact: (OIS_in_inf  (proj32_1 lt) (olt_i lt)).
Qed.

Lemma OFS_in_fin x y: inc x y -> finite_o y -> finite_o x.
Proof.
move=> xy [oy niy]. 
have ox:=(Os_ordinal oy xy).
by split => //; dneg nix; apply: (OIS_in_inf oy xy).
Qed.

Lemma infinite_sP x: ordinalp x ->
  (infinite_o (osucc x) <-> infinite_o x).
Proof.  move=> ox; exact:(succ_inf_aux_ord ox (OS_succ ox)). Qed.


Lemma finite_sP x: finite_o (osucc x) <-> finite_o x.
Proof.
split; move => [p1 p2].
  have ox :=  (OS_succr p1).
  by move: p2 => /(infinite_sP ox) h. 
by split; [ apply: OS_succ | move/(infinite_sP p1)].
Qed.

(** limit ordinals are infinite, since [osucc] is a bijecion for
the least infinite ordinal *)

Lemma OIS_limit x: limit_ordinal x -> infinite_o x.
Proof.
move=> xl.
have hh : z_infinite x by move: xl => [qa qb qc]; split => //.
move:  (z_omega_infinite2 hh) => qd.
exact: (OIS_le_inf  (proj2 (z_omega_limit hh) _ xl) qd).
Qed.

(** The cardinal of [x] is the least ordinal equipotent to [x] *)

Definition cardinal x := 
  (least_ordinal (equipotent x) (ordinal (worder_of x))).

Definition cardinal_prop x y :=
  [/\ ordinalp y,  x \Eq y &
  (forall z, ordinalp z -> x \Eq z -> sub y z)].

Lemma cardinal_unique x y z:
  cardinal_prop x y -> cardinal_prop x z -> y = z.
Proof.
move=> [oy exy p1] [oz exz p2].
by apply: extensionality; [ apply: p1 | apply: p2 ].
Qed.

Lemma cardinal_pr1 x: cardinal_prop x (cardinal x).
Proof.
have [wor sr] :=(proj1 (Zermelo_ter x)).
have [_ _ [bf sf tf] ff]:= (ordinal_isomorphism_exists wor).
apply: (least_ordinal1 (OS_ordinal wor)); exists (ordinal_iso (worder_of x)).
by split => //; ue.
Qed.

Definition cardinalp x:= 
 ordinalp x /\ (forall z, ordinalp z -> x \Eq z -> sub x z).
Definition cardinal_fam x :=  allf x cardinalp.
Definition cardinal_set X :=  alls X cardinalp.

Notation "x =c y" := (cardinal x = cardinal y)
  (at level 70, format "'[hv' x '/ '  =c  y ']'", no associativity).

Lemma card_card x: cardinalp x -> cardinal x = x.
Proof.
move=> [cx1 cx2].
have aux:= (cardinal_pr1 x).
have aux': cardinal_prop x x by split; fprops.
apply: (cardinal_unique aux aux').
Qed.

Lemma oset_cset E: cardinal_set E -> ordinal_set E.
Proof. by move => cx x /cx []. Qed.

Lemma CS_cardinal x: cardinalp (cardinal x).
Proof.
have [p1 p2 p3]:= (cardinal_pr1 x).
split => // z oz ez; apply: (p3 _ oz (EqT p2 ez)).
Qed.

Lemma OS_cardinal x: cardinalp x -> ordinalp x.
Proof. by case.  Qed.

Hint Resolve CS_cardinal: fprops.

Lemma double_cardinal x: cardinal x =c x.
Proof. apply: card_card; fprops. Qed.

Hint Rewrite double_cardinal: aw.

Theorem card_eqP x y:  x =c y <-> x \Eq y.
Proof.
move: (cardinal_pr1 x) (cardinal_pr1 y) => [ox exp lx][oy eyp ly].
split => h; first by  apply: (EqT exp); rewrite h; exact:(EqS eyp). 
apply: extensionality.
  exact: (lx _ oy (EqT h eyp)).
exact: (ly _ ox (EqT (EqS h) exp)).
Qed.


Lemma cardinalP x:
  cardinalp x <-> (ordinalp x /\ forall z, inc z x -> ~ (x \Eq z)).
Proof.
rewrite /cardinalp; split; move=> [ox h]; split => //.
  move => z zx ne; move: ((h _ (Os_ordinal ox zx) ne) _ zx).
  apply: (ordinal_decent ox zx).
move=> z oz exz.
case: (ordinal_inA oz ox) => ty; first by case: (h _ ty). 
  by apply: (ordinal_transitive oz).
by rewrite ty. 
Qed.

Lemma card_ord_le x: ordinalp x -> cardinal x <=o x.
Proof.
move => ox.
move: (cardinal_pr1 x) => [pa pb pc]; split; fprops.
Qed.


Lemma card_bijection f: bijection f -> source f =c target f.
Proof. by move => bf; apply /card_eqP; exists f. Qed.

Lemma cardinal_image f x :  sub x (source f) -> injection f ->
  Vfs f x =c x.
Proof. by move => pa /(Eq_restriction1 pa) /card_eqP.  Qed.

Lemma cardinal_fun_image t g : {inc t &, injective g} -> fun_image t g =c t.
Proof.
move => H; symmetry; apply /card_eqP.
exists (Lf g t (fun_image t g)); saw; apply /lf_bijective.
+ move=> s sa; apply /funI_P; ex_tac.
+ exact H.
+ by move => y /funI_P.
Qed.

Lemma cardinal_range f: injection f -> Imf f =c source f.
Proof. by move /Eq_src_range  /card_eqP. Qed.

Lemma cardinal_indexed a b: a *s1 b =c a.
Proof. symmetry;apply /card_eqP; apply:Eq_indexed.  Qed.

Hint Rewrite cardinal_indexed: aw.

Lemma cardinal_indexedr a b: indexedr b a =c a.
Proof. symmetry;apply /card_eqP; apply:Eq_rindexed.  Qed.

(* We define here zero one and two, and some notations *)

Definition card_zero := emptyset.
Definition card_one := singleton emptyset.
Definition card_two := doubleton emptyset (singleton emptyset).

Definition ord_one := card_one.
Definition ord_two := card_two.

Notation "\0c" := card_zero.
Notation "\1c" := card_one.
Notation "\2c" := card_two.
Notation "\1o" := ord_one.
Notation "\2o" := ord_two.

Lemma osucc_zero: osucc \0o = \1o.
Proof. apply:set0_U2. Qed.

Lemma osucc_one: osucc \1o = \2o.
Proof. exact: setU2_11. Qed.

Lemma olt_01: \0o <o \1o.
Proof. by rewrite - osucc_zero; exact:(oltS OS0). Qed.

Lemma ole_01: \0o <=o \1o.
Proof. exact: (proj1 olt_01). Qed.

Corollary constants_v: (C0 = \0c /\ C1 = \1c /\ C2 = \2c). 
Proof. by []. Qed.

Lemma OS1: ordinalp \1o.
Proof. rewrite - osucc_zero; apply: OS_succ; apply: OS0. Qed.

Lemma OS2: ordinalp \2o.
Proof. rewrite - osucc_one; apply: OS_succ; apply: OS1.  Qed.

Lemma CS0: cardinalp \0c.
Proof. 
by apply/cardinalP; split; [ apply: OS0 | move=> z /in_set0].
Qed.

Lemma cardinal_set0: cardinal emptyset = \0c.
Proof. apply:(card_card CS0). Qed.

Lemma card_nonempty x:
  cardinal x = \0c -> x = emptyset. 
Proof.
rewrite - cardinal_set0; move /card_eqP => [y [[[fy _] suy] sy ty]].
apply /set0_P => z zx; empty_tac1 (Vf y z); Wtac.
Qed.

Lemma card_nonempty0 x: x <> emptyset -> cardinal x <> \0c.
Proof. by move => pa pb; case: pa; apply: card_nonempty. Qed.

Lemma card_nonempty1  x:
  nonempty x -> cardinal x <> \0c.
Proof. by move=> nex; apply :card_nonempty0; apply /nonemptyP. Qed.

Lemma card1_nz: \1c <> \0c.
Proof. fprops. Qed.

Lemma card2_nz: \2c <> \0c.
Proof. exact: (proj1 C2_ne_C01). Qed.

Lemma card_12: \1c <> \2c.
Proof. exact: (nesym (proj2 C2_ne_C01)). Qed.

Hint Resolve card_12 card1_nz card2_nz: fprops.

Lemma gfunctions_empty X: (gfunctions emptyset X) = \1c.
Proof.
apply: set1_pr.
  apply/gfunctions_P2; saw;  fprops; apply fgraph_set0.
by move => z /gfunctions_P2 [_  /domain_set0_P].
Qed.


(** Zero is finite as well as its sucessors *)

Lemma finite_zero: finite_o \0o.
Proof. 
split; first by apply: OS0.
move=> /EqS /card_eqP; rewrite cardinal_set0 osucc_zero. 
move => /card_nonempty; fprops.
Qed.

Lemma finite_one: finite_o \1o.
Proof. rewrite - osucc_zero; apply /finite_sP; apply:finite_zero. Qed.

Lemma finite_two: finite_o \2o.
Proof. by rewrite - osucc_one; apply /finite_sP; apply:finite_one. Qed.

(** If there is injections [E->F] and [F->E], then there are bijections; 
We start with the case [sub F E] *)

Definition cantor_bernstein_bij A B f g :=
  let F := intersection (Zo (\Po A) (fun z =>
     (forall t, inc t z -> inc (Vf g (Vf f t)) z) /\ sub (A -s Imf g) z)) in
  let h := fun x => Yo (inc x F)  (Vf f x) (union (Vfi1 g x)) in
  Lf h A B.

  
Lemma CantorBernstein_eff A B f g:
   injection_prop f A B -> injection_prop g  B A -> 
   bijection_prop (cantor_bernstein_bij A B f g) A B.
Proof.
move => [[ff finj] sf tf] [[fg ginj] sg tg].
have ha x: inc x A -> inc (Vf f x) B  by move => h; Wtac.
have hb x: inc x B -> inc (Vf g x) A  by move => h; Wtac.
rewrite /cantor_bernstein_bij.
set C  := A -s Imf g.
set Z := Zo _ _.
set F := intersection Z.
have sCA: sub C A by move => x/setC_P [].
pose stable x := forall t, inc t x -> inc (Vf g (Vf f t)) x. 
have stableA: stable A by move => t te; fprops.
have iAZ: inc A Z by apply: (Zo_i (setP_Ti A)).
have neZ: nonempty Z by ex_tac.
have sCF: sub C F by move => t ta; apply/(setI_P neZ) => u /Zo_hi/proj2; apply.
have sgE: sub F A by move => t tF; apply:(setI_hi tF iAZ).
have stableF: stable F.
  move => t tG; apply /(setI_P neZ) => u uz; move:(setI_hi tG uz) => tu.
  by move/Zo_hi: uz => /proj1; apply. 
have Ha y : inc y B ->  ~ inc (Vf g y) C.
  move => yF/setC_P [_]; case; apply:(Imf_i fg); ue.
have Hb x: inc x F -> inc x C \/ exists2 y, inc y F & x =  (Vf g (Vf f y)).
  move => xG; case: (inc_or_not x C) => xA; [by left | right]. 
  pose D := F -s1 x.
  case: (all_exists_dichot1 (fun x =>  inc (Vf g (Vf f x)) D) D) => sB.
    have BZ: inc D Z. 
      apply:Zo_i; first by apply/setP_P => t /setC1_P [/sgE].
      split => // t tA; move: (sCF _ tA) => tG; apply/setC1_P; split => // ee.
      by case: xA; rewrite - ee. 
    by case/setC1_1: (setI_hi xG BZ). 
  move: sB =>[y /setC1_P [yG yx]] /setC1_P h.
  case: (equal_or_not x (Vf g (Vf f y))) => xv.
    by exists y=> //; apply: sAG.
  by case: h; split; [  apply: (stableF y yG) | apply:nesym].
rewrite sg in ginj; rewrite sf in finj.
have Hc y: inc y B -> ~inc y (Imf f) -> ~ inc (Vf g y) F.
  move => yF ti /Hb; case; first by apply: Ha.
  move => [x /sgE xE]; move/(ginj _ _ yF (ha _ xE)) => yv. 
  case: ti; rewrite yv; apply: (Imf_i ff); ue.
pose gi x:=  (union (Vfi1 g x)).
have gip x: inc x B -> gi (Vf g x) = x.
    move => xE; rewrite /gi.
    suff:  (Vfi1 g (Vf g x)) = singleton x by move ->; rewrite setU_1.
    apply: set1_pr; first by  apply:(iim_fun_set1_i fg) => //; ue.
    move => t ta; move/ (iim_fun_set1_P (Vf g x) fg): ta => [tsf eq1].
    apply: ginj => //; ue.
have gip2 x: inc x (Imf g) -> inc (gi x) B /\ Vf g (gi x) = x.
  by move /(Imf_P fg) =>[u usg ->]; rewrite sg in usg; rewrite (gip _ usg).
have Pc x: inc x A -> ~inc x F -> inc x (Imf g).
  by move =>  xE xG; ex_middle bad; case: xG; apply: sCF; apply/setC_P.
set h := fun _ => _.
have hf x: inc x F -> h x = Vf f x by  move => xG; rewrite/h; Ytac0.
have hc x: inc x A -> ~(inc x (Imf g)) -> h x = Vf f x.
  by move => pa pb; rewrite /h Y_true //; apply: sCF; apply/setC_P.
have hd x: inc x A -> inc (h x) B.
   move => cE; rewrite /h; Ytac xi; first by apply: ha.
   exact: (proj1(gip2 _ (Pc x cE xi))).
have he x: inc x A -> ~inc x F -> inc (h x) B /\ Vf g (h x) = x.
  move => qa qb; move: (Pc x qa qb) => xg; move: (gip2 x xg) =>[qc qd].
  by rewrite /h; Ytac0.
saw; apply: lf_bijective => //.  
  move => u v uE vE sh.
  case: (inc_or_not u F) => uG;case: (inc_or_not v F) => vG.
  + by move: sh; rewrite /h; Ytac0; Ytac0; apply: finj.
  + by move: (stableF u uG); rewrite - (hf u uG) sh (proj2 (he _ vE vG)). 
  + by move: (stableF v vG); rewrite - (hf v vG) - sh (proj2 (he _ uE uG)). 
  + by rewrite - (proj2 (he _ uE uG))  - (proj2 (he _ vE vG)) sh.
move => y yF.
move: (hb y yF); set x := Vf g y => xE.
case: (inc_or_not y (Imf f)) => yi; last first.
  have yG: ~ inc (Vf g y) F.
    case/Hb; first by apply: Ha.
    move => [z /sgE zE]; move/(ginj _ _ yF (ha _ zE)) => yv. 
    case: yi; rewrite yv; apply: (Imf_i ff); ue.
  by ex_tac; rewrite /h (Y_false yG);rewrite -/(gi _)  (gip y yF).
move/(Imf_P ff):  (yi) =>[z zE zv]; rewrite sf in zE.
case: (inc_or_not z F) => zG.
  by exists z => //; rewrite /h (Y_true zG).
exists x  => //; rewrite /h -/(gi _) (gip y yF) (Y_false) // /x zv => /Hb.
move: (ha z zE) => zF; case; first by apply: Ha.
move =>[t tG]; move: (sgE t tG)=> tE; move/(ginj _ _ zF (ha _ tE)).
by move/(finj _ _ zE tE) => xy; case zG; ue.
Qed.


Definition set_le x y := exists  f,  injection_prop f x y.
Definition set_lt a b := set_le a b /\ ~ (a \Eq b).
Notation "x <=s y" := (set_le x y) (at level 60).
Notation "x <s y" := (set_lt x y) (at level 60).



Theorem CantorBernstein X Y:  X <=s Y -> Y <=s X ->  X \Eq Y.
Proof.
move=> [f fa][g gb].
move: (CantorBernstein_eff fa gb) =>h.
by exists (cantor_bernstein_bij X Y f g).
Qed.


Lemma restriction_fi f x y a: sub a x -> bijection_prop f x y ->
   injection_prop (restriction f a) a y.
Proof.
move =>sax [[[ff ha] _] sf <-].
have sxsf: sub a (source f) by rewrite sf.
move: (restriction_prop ff sxsf) =>[qa qb qc].
split => //; split => // u v; rewrite qb => uv vx.
by rewrite restriction_V // restriction_V //; apply: ha; apply: sxsf.
Qed.

   
Lemma CS_osucc x: finite_o x ->  cardinalp (osucc x).
Proof.
move=> [ox nix]; apply/cardinalP; split; first by apply: OS_succ.
move=> z zo [f fp]; case:nix.
apply: EqT (EqS (equipotent_bp fp)).
have zx: (sub z x) by move/(oleP ox): zo => /proj33.
apply:CantorBernstein.  
  have aux: sub x (osucc x) by rewrite /osucc; fprops.
  exists (restriction f x); exact:(restriction_fi aux fp).
exists (canonical_injection z x); rewrite/canonical_injection;saw.
by  apply: ci_fi.
Qed.


Lemma finite_pred x:  finite_o x -> x <> \0o ->  
   (exists2 y, finite_o y & x = osucc y).
Proof.
move => fx xnz.
case: (ordinal_limA (proj1 fx)).
- done.
- move=> [y oy xK]; rewrite xK; exists y => //; apply/finite_sP;ue.
- move => lim; case: (proj2 fx); apply: (OIS_limit lim).
Qed.


(** a finite ordinal is a cardinal ; so zero, one and two are cardinals *)

Lemma CS_finite_o x: finite_o x -> cardinalp x.
Proof.
move => h; case: (equal_or_not x \0c); first by  move => ->; apply: CS0.
by move/(finite_pred h) => [y yF ->]; apply: CS_osucc.
Qed.

Lemma CS1: cardinalp \1c.
Proof. apply:CS_finite_o; apply:finite_one. Qed.

Lemma CS2: cardinalp \2c.
Proof. apply:CS_finite_o; apply:finite_two. Qed.

Hint Resolve CS0 CS1 CS2 : fprops.

(** We define finite and infinite for sets and cardinals *)

Definition finite_c  :=  finite_o.
Definition infinite_c a := cardinalp a /\ infinite_o a.
Definition finite_set E := finite_c (cardinal E).
Definition infinite_set E := infinite_o (cardinal E).

Lemma infinite_setP x: infinite_set x <-> infinite_c (cardinal x).
Proof.
by move: (CS_cardinal x) => h; split; [ move => h1 | move => [] ].
Qed.

Lemma CS_finite x: finite_c x -> cardinalp x.
Proof. by exact: CS_finite_o. Qed.

Hint Resolve CS_finite: fprops.


Lemma finite_not_infinite x : finite_c x -> ~ infinite_c x.
Proof. by move=> [_ pa][_ pb]. Qed.

Lemma finite_or_infinite x: cardinalp x -> finite_c x \/ infinite_c x.
Proof. 
move => cx; move: (proj1 cx) => ox.
by case: (p_or_not_p (infinite_o x)) => h; [ right |  left ].
Qed.

Lemma finite_not_infinite_set x : finite_set x -> ~ infinite_set x.
Proof.  by move/(finite_not_infinite)=> /infinite_setP. Qed.

Lemma finite_or_infinite_set x: finite_set x \/ infinite_set x.
Proof.
case:(finite_or_infinite (CS_cardinal x)); first by left.
by move/infinite_setP; right.
Qed.

Lemma infinite_nz y:  infinite_c y -> y <> \0c.
Proof.  
by move => iy h; rewrite h in iy;case:(finite_not_infinite finite_zero). 
Qed.

Lemma infinite_card_limit1 x: infinite_c x -> x = opred x.
Proof.
move => icx.
move: icx => [ /cardinalP [ox cyp] iz].
case:  (osuccVpred ox) => // - [y oy yz]. 
have /cyp [] : inc y x by rewrite yz; fprops.
apply: EqS;rewrite yz; apply/ (infinite_sP oy);  ue.
Qed.

Lemma infinite_card_limit2 x: infinite_c x -> limit_ordinal x.
Proof.
move => ic; move: (ic) => [p1 p2]. 
apply/(limit_ordinal_P0 (proj1 (proj1 ic))).
split; last by apply: infinite_card_limit1.
by apply/nonemptyP; apply: infinite_nz.  
Qed. 


(** We define here the cardinal successor *)

Definition csucc_base x := cardinal (osucc x).
Definition csucc := locked csucc_base.

Lemma csuccE x: csucc x = cardinal (osucc x).
Proof. by rewrite /csucc -lock. Qed.

Lemma card_csucc x: csucc x =c osucc x.
Proof. by rewrite csuccE double_cardinal. Qed.
 
Lemma CS_succ a: cardinalp (csucc a).
Proof. rewrite csuccE; fprops. Qed.

Lemma succ_of_finite x: finite_o x -> csucc x = osucc x.
Proof.
by move=> cx; rewrite csuccE (card_card (CS_osucc cx)).
Qed.

Lemma succ_zero: csucc \0c  = \1c.
Proof. rewrite csuccE osucc_zero; apply: card_card; apply: CS1. Qed.

Lemma succ_one: csucc \1c  = \2c.
Proof. rewrite csuccE osucc_one; apply: card_card; apply: CS2. Qed.

Lemma csucc_inf x: infinite_c x <-> x = csucc x.
Proof.
split.
  by rewrite csuccE; move => [sa /card_eqP <- ]; rewrite card_card. 
move => h; rewrite h; split; first by  apply: CS_succ.
apply/card_eqP;rewrite - {2}h; exact: card_csucc.
Qed.

Lemma finite_cP x: finite_c x <->  (cardinalp x /\ x <> csucc x).
Proof.
split.
  by move => fsx;split; [fprops | case/csucc_inf]; case fsx.
move => [cx /csucc_inf xcx]; split; [ exact: (proj1 cx) |  by dneg w].
Qed.

Theorem csucc_inj: {when cardinalp &, injective csucc}.
Proof.
move=> a b ca cb /=; rewrite !csuccE; move /card_eqP.
by move/(succ_inf_aux_ord (proj1 ca) (proj1 cb)) /card_eqP; rewrite ! card_card.
Qed.

Lemma csucc_pr a b: ~ (inc b a) ->
  cardinal (a +s1 b) = csucc (cardinal a).
Proof. 
move=> bna; rewrite csuccE; apply/card_eqP.
have ana := (ordinal_irreflexive (OS_cardinal (CS_cardinal a))).
have [f fp]: a \Eq cardinal a by apply/card_eqP; aw.
by apply:(succ_inf_aux_p1  bna ana); exists f.
Qed.

Lemma csucc_pr1 a b:
  cardinal ((a -s1 b) +s1 b) = csucc (cardinal (a -s1 b)).
Proof. rewrite csucc_pr //; apply: setC1_1. Qed.

Lemma csucc_pr2 a b: inc b a -> 
  cardinal a = csucc (cardinal (a -s1 b)).
Proof. move=> ba; rewrite - {1} (setC1_K ba); apply: csucc_pr1. Qed.

Lemma infinite_set_pr a b: inc b a -> a \Eq (a -s1 b) -> 
  infinite_set a.
Proof.
move=> /csucc_pr2 ba /card_eqP eq; apply/card_eqP.
by  rewrite {1} ba - eq card_csucc. 
Qed.

Lemma infinite_set_pr1 a b: inc b a -> 
  a \Eq (a -s1 b) ->  infinite_set (a -s1 b).
Proof.
move=> ab => h.
move: (infinite_set_pr ab h);rewrite /infinite_set.
by  move /card_eqP:h => <-.
Qed.

Lemma infinite_set_pr2 x: infinite_o x -> ~(inc x x) -> infinite_set x.
Proof.
rewrite /infinite_o/osucc => /EqS eq1 /setU1_K eq2.
rewrite - eq2; apply: infinite_set_pr1 ; [  fprops | ue  ].
Qed.

Lemma infinite_set_pr4 x:infinite_o x -> ordinalp x -> infinite_set x.
Proof. by move => ha /ordinal_irreflexive hb; apply:infinite_set_pr2. Qed.

  
(** We exhibit an infinite set *)

Lemma nat_infinite_set: infinite_set nat.
Proof. 
have zn: inc (Ro 0) nat by apply: R_inc.
set g := IM (fun y:nat => J (Ro y) (Ro (S y))).
have p1: sgraph g by move=> t /IM_P [a ->]; fprops.
have p0: fgraph g.
  split => // x y /IM_P [a ->] /IM_P [b ->]; aw => sp.
  by rewrite sp (R_inj sp).
have p2: nat = domain g.
  set_extens t.
    move=> tn; apply/(domainP p1); exists (Ro (S (Bo tn))).
    apply/IM_P; exists (Bo tn); by rewrite B_eq.
  move=> /(domainP p1) [y] /IM_P [a Je]; rewrite (pr1_def Je); apply: R_inc.
have p3: range g = nat -s1 (Ro 0).
  set_extens t.
    move => /(rangeP p1) [x] /IM_P [a Jeq].
    rewrite (pr2_def Jeq); apply/setC1_P; split; first by apply: R_inc.
    by move=> h; move:(R_inj h). 
  move=> /setC1_P [tn to]; apply/(rangeP p1).
  move:(B_eq tn); move:(Bo tn) => w wv.
  have: w <> 0 by dneg xx; ue.
  rewrite -wv;clear to wv.
  case: w => // n _;  exists (Ro n); apply/IM_P; exists n =>//.
apply: (infinite_set_pr zn).
  exists (triple nat (nat -s1 (Ro 0)) g); saw.
set f := (triple nat (nat -s1 Ro 0) g).
have ff: function f by apply: function_pr => //; rewrite p3.
split; last by apply:(surjective_pr1 ff); rewrite (ImfE ff) /f; aw.
apply: (injective_pr_bis ff) =>// x x' y; rewrite/f; aw.
move =>  /IM_P  [a J1] /IM_P [b J2]. 
rewrite (pr1_def J1)  (pr1_def J2).
move: (pr2_def J1)(pr2_def J2)=> r3 r4.
by rewrite r4 in r3; move: (R_inj r3)=> /eq_add_S ->.
Qed.

(** We consider here the least infinite ordinal; It is an infinite cardinal *)

Definition omega0 := least_ordinal infinite_o (cardinal nat).

Lemma omega0_pr:
   [/\ ordinalp omega0, infinite_o omega0 &
   (forall z, ordinalp z -> infinite_o z -> sub omega0 z)].
Proof.
have p1: ordinalp (cardinal nat).
  by move: (CS_cardinal nat) => [ok _].
by move: (least_ordinal1 p1 nat_infinite_set).
Qed.


Lemma OS_omega: ordinalp omega0.
Proof. exact: (proj31 omega0_pr). Qed.

Hint Resolve OS0 OS1 OS2 OS_omega : fprops.

Lemma OIS_omega: infinite_o omega0.
Proof. exact: (proj32 omega0_pr). Qed.

Lemma CS_omega: cardinalp omega0.
Proof.
move: omega0_pr => [qa qb qc]; split => // z oz eq; apply: (qc _ oz).
by apply:(EqT (EqT (EqS eq) qb)); apply /(succ_inf_aux_ord qa oz).
Qed.

Lemma CIS_omega: infinite_c omega0.
Proof. split; [ apply: CS_omega | apply: OIS_omega]. Qed.

Lemma omega_limit0: omega0 = opred omega0.
Proof. apply:(infinite_card_limit1 CIS_omega). Qed.

Lemma omega_limit: limit_ordinal omega0.
Proof. exact:(infinite_card_limit2 CIS_omega). Qed.

Lemma omega_rec (p: property):
  p \0o ->  (forall x, inc x omega0 -> p x -> p (osucc x)) ->
  forall x, inc x omega0 -> p x.
Proof.
have ho: z_infinite omega0 by case: omega_limit.
move: omega0_pr => [qc qd qe].
move: (z_omega_prop ho) (z_omega_ordinal ho) (z_omega_rec ho) => [qa qb] qf.
rewrite - (extensionality (qe _ qf (z_omega_infinite2 ho))  (qb _ ho)).
apply.
Qed.

Lemma omega_P1 x: ordinalp x -> 
  (infinite_o x <->  sub omega0 x).
Proof.
move=> ox; split; first by apply:(proj33 omega0_pr).
move => sox; exact : (OIS_le_inf (And3 OS_omega ox sox) OIS_omega).
Qed.

Lemma omega_P2 x: inc x omega0 <-> finite_o x.
Proof.
split.
  move => xo; have ox:= (Os_ordinal OS_omega xo).
  split=>// /(omega_P1 ox) h.
  case: (ordinal_irreflexive ox (h _ xo)).
by move => [ox /(omega_P1 ox) nifx]; case:(oleT_si OS_omega ox). 
Qed.

Lemma limit_ge_omega x: limit_ordinal x -> omega0 <=o x.
Proof.
move=> ln;move: OS_omega (ln) => oo [ox _ _]. 
by move /(omega_P1 ox):(OIS_limit ln); split. 
Qed.


(** Some properties of infinite sets *) 
Lemma omega_limit3 x: infinite_c x -> sub omega0 x.
Proof.
by move => h;case:(limit_ge_omega (infinite_card_limit2 h)).
Qed.


Lemma infinite_set_pr3 x: omega0 <=o x -> infinite_set x.
Proof.
by  move => [p1 p2 p3]; apply: (infinite_set_pr4 _ p2); apply /omega_P1.
Qed.

End Bordinal.

Export Bordinal.

Module Cardinal.

(** ** EIII-3-1 The cardinal of a set *)



(** Singletons are equipotent, as well as doubletons *)

  
Lemma Eq_set1 x : singleton x \Eq C1.
Proof.
exists (Lf (fun _ => C0) (singleton x) C1); saw.
apply:lf_bijective.
- move => t _; apply:set1_1.
- by move => u v /set1_P -> /set1_P -> _.
- move => y /set1_P ->; exists x => //; fprops.
Qed.


Lemma cardinal_set1 x: cardinal (singleton x) = \1c.
Proof. 
by move/card_eqP:(Eq_set1 x); rewrite -(card_card CS1).
Qed.

Lemma cardinal_set2 x x': x <> x' -> cardinal (doubleton x x') = \2c.
Proof.
move =>  /set2_equipotent_aux /proj31;set g := Lf _ _ _ => bg.
by rewrite -(card_card CS2);apply /card_eqP; exists g.
Qed.

Lemma set_of_card_oneP x: cardinal x = \1c <-> singletonp x.
Proof.
split; last by move => [y ->]; apply:cardinal_set1.
move/esym; rewrite -(card_card CS1); move /card_eqP; rewrite /card_one.
move=> [f [[[ff injf] sf] srf <-]]; exists (Vf f emptyset).
apply: set1_pr; first by Wtac; rewrite srf;fprops.
move => z /(proj2 sf) [y]; rewrite srf; move=> /set1_P -> <-; fprops.
Qed.

Lemma set_of_card_twoP x: cardinal x = \2c  <-> doubletonp x.
Proof.
split; last by move => [a [b [nab ->]]]; apply: cardinal_set2.
move/esym;rewrite -(card_card CS2); move /card_eqP.
move=> [f [[[ff injf] [_ sf]] srf <-]]. rewrite srf in injf sf.
have es: inc \0c \2c by fprops.
have ses: inc \1c \2c by fprops.
exists (Vf f \0c), (Vf f \1c); split.
  by move=> aux; move: (injf _ _ es ses aux); fprops.
set_extens t.
  move /sf => [z zsf ->]; case/set2_P:zsf => ->; fprops.
case /set2_P => ->; Wtac.
Qed.

(** Equipotency is compatible with products *)

Definition equipotent_ex E F := 
   choose (fun z=>  bijection_prop z E F).

Lemma equipotent_ex_pr E F:
  E \Eq F -> bijection_prop (equipotent_ex E F) E F.
Proof. by move/choose_pr. Qed.

Lemma equipotent_ex_pr1 E F:
  E =c F -> bijection_prop (equipotent_ex E F) E F.
Proof. by move/card_eqP => / equipotent_ex_pr. Qed.


Definition fgraphs_equipotent x y := 
  domain x = domain y  
  /\ (forall i, inc i (domain x) ->  (Vg x i) =c (Vg y i)).



Lemma Eqc_setXb x y: 
  fgraphs_equipotent x y -> (productb x) =c (productb y).
Proof. 
move=> [dxy ale].
pose g i := equipotent_ex (Vg x i) (Vg y i).
pose f i :=  graph (g i).
rewrite  -(productb_gr x) - (productb_gr y) - dxy.
apply/card_eqP;exists (ext_map_prod (domain x) (Vg x) (Vg y) f).
hnf; rewrite /ext_map_prod; saw.
have ea: ext_map_prod_axioms (domain x) (Vg x) (Vg y) f.
  move=> i iI; move: (equipotent_ex_pr1 (ale _ iI))=> [[[fg _] _] sg tg].
  rewrite /f; split; fprops.
    by rewrite - sg; apply: domain_fg.
  by rewrite -tg;apply: f_range_graph.
split.
  apply: ext_map_prod_fi =>// i iI.
  move: (equipotent_ex_pr1 (ale _ iI)) => /proj31 /proj1.
  by rewrite -/(g _); move => [ [_ qa qb] qc]; split => //; rewrite -  qb.
apply:  ext_map_prod_fs =>//.
move=> i iI;  move: (equipotent_ex_pr1 (ale _ iI)) => [[ig sg] _ p4].
by rewrite /f -p4 - (surjective_pr0 sg) (ImfE (proj1 sg)).
Qed.

Lemma Eqc_setX a b a' b':
  a =c a' -> b =c b' -> (a \times b) =c (a' \times b').
Proof. 
move => /card_eqP [f [bf <- <-]] /card_eqP [f' [bf' <- <-]]; apply/card_eqP.
move:(ext_to_prod_fb bf bf') => h.
by exists  (f \ftimes f'); split => //; rewrite /ext_to_prod; aw.
Qed.


(** Properties of disjoint sets *)


Lemma Eqc_disjointU X Y:
  fgraphs_equipotent X Y ->
  mutually_disjoint X ->  mutually_disjoint Y ->
  (unionb X) =c (unionb Y).
Proof. 
move=> [dXY ale] mX mY.
pose g i := equipotent_ex (Vg X i) (Vg Y i).
set X' := (Lg (domain X) (Vg X)).
have pfX: partition_w_fam X' (unionb X). 
   rewrite /X';split; fprops.
     by hnf; aw; move => a b ax bx; rewrite !LgV //; apply: mX.
   by rewrite (unionb_gr X).
pose h i :=  triple (source (g i)) (unionb Y) (graph (g i)).
have fph: forall i, inc i (domain X')-> function_prop (h i)(Vg X' i) (unionb Y).
  rewrite /X'; aw; move=> i idx; aw.
  move: (equipotent_ex_pr1 (ale _ idx)) =>  [[[fg _] _] sg tg].
  hnf;rewrite /h; aw; rewrite LgV //; split => //. 
  apply: function_pr; fprops.
    apply:  (@sub_trans  (target (g i))). 
      by apply: f_range_graph.
    rewrite tg; move=> t tf; union_tac; ue. 
  by rewrite domain_fg.
move:(extension_partition1 pfX fph). 
set x := common_ext _ _ _;move=> [[fx sx tx] agx'].
have agx:forall i, inc i (domain X) -> agrees_on (Vg X i) x (h i).
  by move: agx'; rewrite /X';aw => h1 i idx; move: (h1 _ idx); rewrite LgV.
apply/card_eqP; exists x; split => //.
split; split=>//.
  rewrite sx;move=> a b /setUb_P [i idX ai] /setUb_P [j jdX bj].
  have ->: Vf x a = Vf (g i) a.
    by move:(agx _ idX) => [_ _ ha];rewrite (ha _ ai) /Vf /h; aw.
  have ->: Vf x b = Vf (g j) b.
    by move:(agx _ jdX) => [_ _ hb];rewrite (hb _ bj) /Vf /h; aw.
  move: (equipotent_ex_pr1 (ale _ idX)) => [[[fg ig] _] sg tg].
  move: (equipotent_ex_pr1 (ale _ jdX)) => [[[fg' _] _] sg' tg'].
  have Wta: (inc (Vf (g i) a) (Vg Y i)) by rewrite -tg /g ; Wtac.
  have Wtb: (inc (Vf (g j) b) (Vg Y j)) by rewrite - tg' /g; Wtac.
  rewrite dXY in idX jdX.
  case: (mY _ _ idX jdX) => eq.
     rewrite -eq in bj |- * ; apply: ig; ue. 
  move=> eq'; rewrite -eq' in Wtb.
  by red in eq;empty_tac1 (Vf (g i) a ).
rewrite tx=> y /setUb_P; rewrite -dXY; move=> [i idX yV].
move: (equipotent_ex_pr1 (ale _ idX))  =>  [[_ sg] srg tg].
rewrite -tg in yV; move: ((proj2 sg) _  yV) => [z zsg Wg].
move: (agx _ idX)=> [s1 s2 v].
exists z; first by apply: s1; ue.
by rewrite srg in zsg;  rewrite v// Wg /Vf /h; aw.
Qed.

Lemma Eq_indexed_c a b: (a *s1 b) =c a.
Proof. symmetry;apply/card_eqP/Eq_indexed. Qed.

Lemma Eqc_disjointU1 X Y:
  fgraphs_equipotent X Y ->
  (disjointU X) =c (disjointU  Y).
Proof. 
move=> [pc pd].
apply: Eqc_disjointU; rewrite /fgraphs_equipotent; fprops.
split; rewrite/disjointU_fam -? dXY; aww.
by  move=> i idy; rewrite !LgV//; fprops; try ue; rewrite !Eq_indexed_c pd.
Qed.




Lemma Eqc_disjointU2 a b a' b':
  disjoint a b -> disjoint a' b' -> a =c a' -> b =c b' ->
  (a \cup b) =c (a' \cup b').
Proof.
move=> dab dab' eqq' ebb'.
rewrite ! union2Lv; apply:Eqc_disjointU; try apply: disjointLv =>//.
by hnf;saw => // i ind; try_lvariant ind.
Qed.

Definition doubleton_fam f a b :=
 [/\ fgraph f, doubletonp (domain f) & range f = doubleton a b].

Lemma doubleton_C2: doubletonp C2.
Proof. exists C0, C1; split; fprops. Qed.
  
Lemma doubleton_fam_canon f:
  doubleton_fam (Lg C2 f) (f C0) (f C1).
Proof.
split; fprops;aw;[ apply: doubleton_C2 | by rewrite Lg_range funI_set2].
Qed.

Lemma doubleton_fam_variant x y a b: y <> x ->
  doubleton_fam (variantL x y a b) a b.
Proof. 
rewrite /variantL => xny; split; aw; fprops; first by exists x,y; split; fprops.
by rewrite Lg_range funI_set2 variant_true // variant_false.
Qed.

Lemma doubleton_fam_rev a b:
  doubleton_fam (variantLc b a) a b.
Proof.
split; fprops; first by  aw; apply: doubleton_C2.
by rewrite Lg_range funI_set2 variant_true1 variant_false1 set2_C.
Qed.

Lemma two_terms_bij a b f (F:= variantLc a b) : doubleton_fam f a b ->
  exists g, [/\ bijection g, target g = domain F & f = F \cf (graph g)].
Proof.
move =>  [fgf [x [y [xy df]]] rf].
wlog [qa qb]: x y df xy / Vg f x = a /\ Vg f y = b.
  move => hyp.
  move: (set2_1 a b)(set2_2 a b); rewrite - rf.
  move => /(range_gP fgf) [u udf av] /(range_gP fgf) [v vdf bv].
  move: udf vdf; rewrite df => /set2_P a1 /set2_P a2.
  case: (equal_or_not u v) => cuv.
    apply: (hyp x y) => //.
    move: (set2_1 x y)(set2_2 x y); rewrite - df => xdf ydf.
    move: (inc_V_range fgf xdf) (inc_V_range fgf ydf); rewrite rf.
    by rewrite av bv cuv => /set1_P -> /set1_P ->.
  case: a1 => uv; case: a2 => vv.
  + by case: cuv; rewrite uv vv.  
  + by apply: (hyp x y) => //; rewrite - uv - vv av bv.
  + by apply: (hyp y x);[rewrite set2_C | apply: nesym | rewrite - uv - vv av bv].
  + by case: cuv; rewrite uv vv.  
move:(set2_equipotent_aux xy); set g := Lf _ _ _; move => [[bg sg tg] ga gb].
rewrite /F;exists g;split;fprops; first by aw.
move: (domain_fg (proj1 (proj1 bg))); rewrite sg => dg.
apply: fgraph_exten; fprops. 
  by rewrite /composef; aw; rewrite dg.
rewrite /composef dg.
rewrite df => z; case /set2_P => ->;  rewrite LgV //; fprops.
  by rewrite -/(Vf g x) ga; aw.
by rewrite -/(Vf g y) gb; aw.
Qed.


(** ** EIII-3-2 Order relation between cardinals *)

Definition equipotent_to_subset x y:= exists2 z, sub z y & x \Eq z.


Lemma set_leP a b: a <=s b <-> equipotent_to_subset a b.
Proof.
rewrite/equipotent_to_subset; split.
  move=> [f [injf srf tgf]].
  exists (Imf f). 
    rewrite -tgf; apply: Imf_Starget; fct_tac.
  by rewrite /Imf - srf; apply:(Eq_restriction1 _ injf).
move=> [z zy [f [[injf srj] sf tf]]].
exists ((canonical_injection z b) \co f).
hnf; rewrite /canonical_injection; aw; split => //.
by apply: inj_compose1=>//; [apply: ci_fi=>// | aw].
Qed.

Lemma set_le_t a b: sub a b -> a <=s b.
Proof. move => ab; apply/set_leP; exists a; fprops. Qed.
  
Lemma eq_subset_pr2 a b a' b':
   a =c a' -> b =c b' ->  a <=s b -> a' <=s b'.
Proof.
move=> /card_eqP /EqS [g [[injg _] sg tg]] /card_eqP [f [[injf _] sf tf]].
move => [h [ih sh th]]; exists ((f \co h) \co g); split => //; aw; trivial.
have ch: f \coP h by split => // ;try fct_tac; ue.
apply: compose_fi => //. 
  apply: compose_fi => //.  
by split => //; try fct_tac; aw; ue.
Qed.

Lemma eq_subset_cardP x y:
  x <=s y <->  (cardinal x) <=s (cardinal y).
Proof.
move:(double_cardinal x) (double_cardinal y) => ha hb.
split; last exact: (eq_subset_pr2 ha hb).
symmetry in ha; symmetry in hb;  exact: (eq_subset_pr2 ha hb).
Qed.

Definition cardinal_le x y := 
  [/\ cardinalp x, cardinalp y & sub x y].
Definition cardinal_lt a b := cardinal_le a b /\ a <> b.


Notation "x <=c y" := (cardinal_le x y) (at level 60).
Notation "x <=cc y" := (cardinal x <=c cardinal y) (at level 60).
Notation "x <c y" := (cardinal_lt x y) (at level 60).

Lemma ocle x y: x <=c y -> x <=o y.
Proof. by move=> [[ox _] [oy _] le]. Qed.

Lemma cardinal_le_aux1 x y:
  x <=c y ->  x <=s y.
Proof. by move => [_ _ /set_le_t]. Qed.

Lemma cardinal_le_aux2P x y: cardinalp x -> cardinalp y ->
  (x <=s y <-> x <=c y).
Proof.
move=> cx cy.
split; last by apply: cardinal_le_aux1.
move => /set_leP [z zy ezx]; split => //.
case:(oleT_ee (OS_cardinal cx)(OS_cardinal cy)) => []  [_ _ ] => // syx.
suff: y \Eq x. 
  by move/card_eqP; rewrite  (card_card cx) (card_card cy) => ->.
apply:(CantorBernstein (set_le_t syx)).
by apply/set_leP; exists z.
Qed.

Lemma eq_subset_cardP1 x y:x <=s y <-> x <=cc y.
Proof.
apply: (iff_trans (eq_subset_cardP x y)).
split; first by  move/cardinal_le_aux2P; apply; fprops.
apply: cardinal_le_aux1.
Qed.

Lemma sub_smaller a b:  sub a b -> a <=cc b.
Proof. by move=> /set_le_t ab; apply /eq_subset_cardP1. Qed.

Lemma sub_smaller_contra Z X: Z <=cc  X -> 
   exists2 Y, sub Y X & cardinal Z = cardinal Y.
Proof. by move => /eq_subset_cardP1/set_leP [y yx /card_eqP h]; exists y. Qed.

Lemma inj_source_smaller f: injection f -> (source f) <=cc (target f).
Proof. 
move => injf; rewrite - (cardinal_range injf).
apply:(sub_smaller (Imf_Starget (proj1 injf))).
Qed.


Lemma cleR x: cardinalp x -> x <=c x.
Proof. by move=> cx;split. Qed.

Hint Resolve cleR: fprops.

Lemma cleT b a c: a <=c b -> b <=c c -> a <=c c.
Proof.  
by move=> [ca cb eab] [_ cc ebc]; split => //; apply: sub_trans eab ebc. 
Qed.

Lemma cleA x y: 
  x <=c y -> y <=c x -> x = y.
Proof. 
by move =>  [ca cb eab] [_ cc ebc]; apply: extensionality.
Qed.

Lemma cle_wor' E (x:= intersection E): cardinal_set E -> nonempty E ->
   inc x E /\ (forall y, inc y E -> x <=c y).
Proof.
move => sa sb.
have sc:= oset_cset sa.
move: (ordinal_setI sb sc) => xe; split => //.
by move => y yE; split; [apply: sa | apply: sa| apply:setI_s1].
Qed.


Theorem cle_wor: worder_r cardinal_le.
Proof.
split => //.
  split => //.
  - move=> a b c;apply: cleT.
  - move=> a b; apply: cleA.
  - move=> x y [cx cy _]; split; fprops.
move=> x xa xne.
have xc: cardinal_set x by move=> b bx; move: (xa _ bx)=> [ok _].
have [ip ii]:=(cle_wor' xc xne); exists (intersection x).
hnf; rewrite (graph_on_sr xa); split => //.
by move=> u ux;move: (ii _ ux) => uy; apply graph_on_P1.
Qed.


(** The order on cardinals *)

Lemma cle_eqVlt a b : a <=c b -> (a = b \/ a <c b).
Proof.
move => h1; case: (equal_or_not a b) => h2; [by left | by right ].
Qed.

Lemma cleNgt a b: a <=c b -> ~(b <c a).
Proof. by move=> ab [ba nba]; case: nba; apply: cleA.
Qed.

Lemma cltNge a b: a <c b -> ~(b <=c a).
Proof. move => ha hb; exact: (cleNgt hb ha). Qed.

Lemma clt_leT b a c: a <c b -> b <=c c -> a <c c.
Proof. 
move=> [ab nab] bc; split; first exact: (cleT ab bc). 
by dneg ac;  rewrite -ac in bc; apply: cleA.
Qed.

Lemma cle_ltT b a c:  a <=c b -> b <c c -> a <c c.
Proof. 
move=> ab [bc nbc]; split; first by exact: (cleT ab bc). 
by dneg ca;  rewrite ca in ab; apply: cleA.
Qed.

Lemma clt_ltT a b c: a <c b -> b <c c -> a <c c.
Proof. move => h1 [h2 _]; exact: (clt_leT h1 h2). Qed.


Lemma wordering_cle_pr x:
  cardinal_set x ->
  (worder_on (graph_on cardinal_le x) x).
Proof. 
move=> alc; apply: (wordering_pr cle_wor).
move=> a ax; move: (alc _ ax); fprops.
Qed.

Lemma cleT_ell a b: 
  cardinalp a -> cardinalp b ->  [\/ a = b, a <c b | b <c a].
Proof. 
move=> ca cb.
move: (ca)(cb) => [oa _] [ob _].
case: (ordinal_inA oa ob) => h.
- by constructor 2; move: (ordinal_sub2 ob h) => [p1 p2]. 
- by constructor 3; move: (ordinal_sub2 oa h) => [p1 p2]. 
- by constructor 1.
Qed.

Lemma cleT_el a b:
  cardinalp a -> cardinalp b ->  a <=c b \/ b <c a.
Proof. 
move=> ca cb; case: (cleT_ell ca cb).
+ move=> ->; left; fprops.
+ by move => [p1 _]; left.
+ by right.
Qed.

Lemma cleT_ee a b:
  cardinalp a -> cardinalp b ->  a <=c b \/ b <=c a.
Proof. 
move=> ca cb; case: (cleT_el ca cb); [by left | by move =>[p1 _]; right ].
Qed.


(** Min and max *)
Definition cmax:= Gmax cardinal_le.
Definition cmin:= Gmin cardinal_le.

Lemma CS_cmax x y: cardinalp x -> cardinalp y -> cardinalp(cmax x y).
Proof. by apply:Gmax_S. Qed.

Lemma CS_cmin x y: cardinalp x -> cardinalp y -> cardinalp(cmin x y).
Proof. by apply:Gmin_S. Qed.

Lemma cmax_xy x y: x <=c y -> cmax x y = y.
Proof. by apply:Gmax_xy. Qed.

Lemma cmax_yx x y: y <=c x -> cmax x y = x.
Proof. apply: (Gmax_yx cleA). Qed.
 
Lemma cmin_xy x y: x <=c y -> cmin x y = x.
Proof. by apply: Gmin_xy. Qed.

Lemma cmin_yx x y: y <=c x -> cmin x y = y.
Proof. apply: (Gmin_yx cleA). Qed.  

Lemma cmaxC x y: cardinalp x -> cardinalp y -> cmax x y = cmax y x.
Proof. apply: (GmaxC cleA cleT_ee). Qed.

Lemma cminC x y: cardinalp x -> cardinalp y -> cmin x y = cmin y x.
Proof. apply: (GminC cleA cleT_ee). Qed.

Lemma cmax_p1 x y:  cardinalp x -> cardinalp y ->
   x <=c (cmax x y) /\ y <=c (cmax x y).
Proof. apply:(Gmax_p1 cleA cleR cleT_ee). Qed.

Lemma cmin_p1 x y:  cardinalp x -> cardinalp y ->
   (cmin x y)  <=c x /\ (cmin x y) <=c y.
Proof. apply:(Gmin_p1 cleA cleR cleT_ee). Qed.


Lemma cmax_p0 x y z: x <=c z -> y <=c z -> (cmax x y) <=c z.
Proof. apply:Gmax_p0. Qed.

Lemma cmin_p0 x y z: z <=c x -> z <=c y -> z <=c (cmin x y).
Proof.  apply:Gmin_p0. Qed.

Lemma cmaxA x y z: cardinalp x -> cardinalp y -> cardinalp z -> 
    cmax x (cmax y z) = cmax (cmax x y) z.
Proof. apply: (GmaxA  cleA cleR cleT cleT_ee). Qed.

Lemma cminA x y z: cardinalp x -> cardinalp y -> cardinalp z -> 
    cmin x (cmin y z) = cmin (cmin x y) z.
Proof. apply: (GminA  cleA cleR cleT cleT_ee). Qed.
 
Lemma cminmax x y z: 
  cardinalp x -> cardinalp y -> cardinalp z ->
  cmin x (cmax y z) = cmax (cmin x y) (cmin x z).
Proof. apply: (Gminmax  cleA cleR cleT cleT_ee). Qed.

Lemma cmaxmin x y z: 
  cardinalp x -> cardinalp y -> cardinalp z ->
  cmax x (cmin y z) = cmin (cmax x y) (cmax x z).
Proof.  apply: (Gmaxmin cleA cleR cleT cleT_ee). Qed.

Lemma ocle3 x y: 
   cardinalp x -> cardinalp y -> x <=o y -> x <=c y.
Proof. by move => cx cy [_ _ h]; split. Qed.

Lemma oclt3 x y: 
   cardinalp x -> cardinalp y -> x <o y -> x <c y.
Proof. by move=> cx cy [le ne]; split => //; apply: ocle3. Qed.

Lemma cardinal_pr3 a: ordinalp a -> cardinal a <=o a.
Proof.
move => oa.
by have [h1 h2]:=(CS_cardinal a); split => //; apply/(h2 _ oa)/card_eqP; aw.
Qed.  


Lemma colt1 a x: cardinalp x -> inc a x -> cardinal a <c x.
Proof.
move => cx ax; apply: (oclt3 (CS_cardinal a) cx).
move/(oltP (OS_cardinal cx)): (ax) => lt1; move:(proj31_1 lt1) => oa.
exact:(ole_ltT (cardinal_pr3 oa) lt1).
Qed.

Lemma ocle1 x y: x <=o y ->  x <=cc y.
Proof.
by move => [_ _  pc]; apply /eq_subset_cardP1; apply: set_le_t.
Qed.

Lemma oclt x y: x <c y -> x <o y.
Proof. by move=> [pa pb];split => //; apply: ocle. Qed.

Lemma ocle2P x y:  cardinalp x ->  ordinalp y ->
  ((y <o x) <-> (cardinal y <c x)).
Proof. 
move=> cx oy; rewrite -{2} (card_card cx).
move: cx => [ox xp].
split; move => [p1 p2].
  move: (ocle1 p1) => p5; split => //; dneg p3.
  by apply: (oleA p1); split => //; apply: (xp _ oy); apply/card_eqP. 
case: (oleT_el ox oy) => // p3.
move: (ocle1 p3)=> r1;case: p2; apply:cleA p1 r1.
Qed.

Lemma ordinals_card_ltP y: cardinalp y ->
  forall x, inc x y <-> (ordinalp x /\ (cardinal x) <c y).
Proof.
move => cy x; move: (proj1 cy) => oy.
split.
  move /(oltP oy) => xy;move: (proj31_1 xy) => ox;split => //.
  by apply /(ocle2P cy ox).
by move => [ox]; move /(ocle2P cy ox) /(oltP oy).
Qed.


Lemma infinite_c_P2 x: infinite_c x <->  (omega0 <=c x).
Proof.
move: CS_omega => h; split.
  by move=> [pa pb]; split => //; apply /(omega_P1 (OS_cardinal pa)). 
by  move=> [pa pb pc]; split => //; apply  /(omega_P1 (OS_cardinal pb)).
Qed.


Lemma finite_c_P2 x: finite_c x <-> (x <c omega0).
Proof.
split; last by move => /oclt/olt_i /omega_P2.
move => fa.
apply: (oclt3 (CS_finite fa) CS_omega). 
by apply/(oltP OS_omega); apply/omega_P2. 
Qed.


Lemma clt_fin_inf a b: finite_c a -> infinite_c b -> a <c b.
Proof. by move=> /finite_c_P2 fa /infinite_c_P2; apply:clt_leT. Qed.

Lemma cle_fin_inf a b: finite_c a -> infinite_c b -> a <=c b.
Proof. 
move=> fa ib; exact: (proj1 (clt_fin_inf fa ib)).
Qed.

Lemma cle_inf_inf a b: infinite_c a -> a <=c b -> infinite_c b.
Proof.
by move => /infinite_c_P2 sa sb; apply/infinite_c_P2; apply: (cleT sa sb).
Qed.

Theorem cle_fin_fin a b:  finite_c b -> a <=c b -> finite_c a.
Proof. 
move=> /finite_c_P2 hb ha; apply/finite_c_P2; exact: (cle_ltT ha hb).
Qed.

Lemma sub_image_finite_set A B f:
  finite_set B -> (forall x, inc x A -> inc (f x) B) ->
  {inc A &, injective f} ->
  finite_set A.
Proof.
move => fsb fa fb. 
have h: injection (Lf f A B) by apply: lf_injective.
by move:(inj_source_smaller h); aw; apply: cle_fin_fin.
Qed.

Lemma sub_finite_set x y: sub x y -> finite_set y -> finite_set x.
Proof. 
move => xy fy; apply: (cle_fin_fin fy (sub_smaller xy)).
Qed.


Section OrdinalFinite.
Variable x:Set.
Hypothesis ox: ordinalp x.

Lemma ordinal_finite1: finite_set x -> finite_o x.
Proof.
move => fsx;split => //.
move/(omega_P1 ox)=> infc.
move: (sub_finite_set infc fsx) =>/finite_c_P2.
by rewrite (card_card CS_omega); case. 
Qed.


Lemma ordinal_finite4: infinite_set x -> omega0 <=o x.
Proof.
move/infinite_setP/infinite_c_P2 /ocle => h; exact:(oleT h (cardinal_pr3 ox)).
Qed.

Lemma ordinal_finite2: infinite_set x -> infinite_o x.
Proof. by move/ordinal_finite4 => /proj33 /(omega_P1 ox). Qed.

Lemma ordinal_finite3: finite_set x -> x <o omega0.
Proof.
move=> ifs; apply /oltP0; split; fprops.
by apply /omega_P2; apply: ordinal_finite1.
Qed.

End OrdinalFinite.


(** Properties of 0 and 1 *)


Lemma oge1P x:  (\1o <=o x) <-> (\0o <o x).
Proof. rewrite - osucc_zero;apply:iff_sym; exact:oleSltP. Qed.

Lemma oge1 x: ordinalp x -> x <> \0o -> \1o <=o x.
Proof. by move=> ox xne; apply/oge1P; apply: ord_ne0_pos. Qed.

Hint Resolve oge1 : fprops.

Lemma olt1 x:  x <o \1o -> x = \0o.
Proof. by move/(oltP OS1) /set1_P. Qed.

Lemma olt2 a: a <o \2c ->  a = \0o \/ a = \1o.
Proof.  by move/(oltP OS2)/set2_P. Qed.


Lemma ozero_dichot x: ordinalp x -> x = \0o \/ \0o <o x.
Proof.
move => ox; case: (equal_or_not x \0o) => xe; first by left. 
by right; apply: ord_ne0_pos.
Qed.

Lemma oone_dichot x y: x <o y -> (y = \1o \/ \1o <o y).
Proof.
move => h; case: (equal_or_not y \1o) => h'; [by left | right; split; fprops].
apply: oge1; [exact : (proj32_1 h) | move=> h''; case: (@olt0 x); ue].
Qed.

Lemma cle0x x: cardinalp x -> \0c <=c x.
Proof. 
move=> cx; rewrite - cardinal_set0 - (card_card cx).
apply: sub_smaller; fprops.
Qed.

Lemma czero_dichot x: cardinalp x -> x = \0c \/ \0c <c x.
Proof.
move => ox; case: (equal_or_not x \0c) => xz; [by left | right].
split; [ exact:cle0x | exact:nesym].
Qed.  


Lemma cle0 a: a <=c \0c -> a = \0c.
Proof. 
move=> alez; exact:(cleA alez (cle0x (proj31 alez))).
Qed.

Lemma clt0 x: x <c \0c -> False.
Proof. by move=> [pa pab]; move: (cle0 pa). Qed.

Lemma card_ne0_pos x: cardinalp x -> x <> \0c -> \0c <c x.
Proof. move => cx xnz; split => //; [ by apply: cle0x | fprops]. Qed.

Lemma card_gt_ne0 x y: x <c y -> y <> \0c.
Proof. move => xy yz; rewrite yz in xy; exact: (clt0 xy). Qed.

Lemma succ_nz n: csucc n <> \0c.
Proof. rewrite csuccE; apply: card_nonempty1;  exists n; fprops. Qed.

Lemma succ_positive a: \0c <c (csucc a).
Proof. 
split; first by apply: cle0x;  apply: CS_succ. 
exact: (nesym(@succ_nz a)).
Qed.

Lemma clt_01: \0c <c \1c.
Proof. rewrite - succ_zero; apply: succ_positive. Qed.

Lemma cle_01: \0c <=c \1c.
Proof. exact: (proj1 clt_01). Qed.

Hint Resolve cle_01 clt_01 : fprops.

Lemma cle_12: \1c <=c \2c.
Proof. by split; fprops => // t /set1_P ->; apply:set2_1. Qed.

Lemma clt_12: \1c <c \2c.
Proof. split; [ exact:cle_12 | fprops ]. Qed.

Lemma clt_02: \0c <c \2c.
Proof. exact: (clt_ltT clt_01 clt_12). Qed.

Lemma cge1P x:  (\1c <=c x) <-> (\0c <c x).
Proof.
split; move=> le1;first exact:(clt_leT (clt_01) le1).
by apply: (ocle3 CS1 (proj32_1 le1)); apply /oge1P; exact: (oclt le1).
Qed.

Lemma clt1  x: x <c \1c -> x = \0c.
Proof. by move=> /oclt/olt1. Qed.

Lemma cge1 x: cardinalp x -> x <> \0c -> \1c <=c x.
Proof. by move => sa sb; apply /cge1P; apply:card_ne0_pos. Qed.

Lemma clt2 a: a <c \2c ->  a = \0c \/ a = \1c.
Proof. by move/oclt/olt2. Qed.

Lemma cge2 x: cardinalp x -> x <> \0c ->  x <> \1c  -> \2c <=c x.
Proof.
by move => cx x0 x1; case: (cleT_el CS2 cx) => //;case /clt2.
Qed.

Lemma cle1P E: \1c <=c (cardinal E) <-> nonempty E.
Proof. 
split.
  move => h; case: (emptyset_dichot E) => // h1.
  case:(cleNgt h); rewrite h1 (cardinal_set0); exact:clt_01.
move=> /card_nonempty1 nE; apply: cge1;fprops. 
Qed.

Lemma cle2P E:
  \2c <=c (cardinal E) 
  <-> exists a b, [/\ inc a E, inc b E & a <> b].
Proof.
split.
  rewrite - (card_card CS2) => /cardinal_le_aux1/(eq_subset_cardP \2c).
  move => /set_leP [x xE] => /card_eqP. rewrite (card_card CS2) => /esym.
  move/set_of_card_twoP => [a [b [anb xv]]].
  exists a,b; split => //; apply: xE; rewrite xv; fprops.
move => [x [y [xE yE nxy]]].
have sE: (sub (doubleton x y) E) by move=> t td; case/set2_P: td =>->; fprops. 
by rewrite - (cardinal_set2 nxy); apply: sub_smaller.
Qed.

(** There is a set containing all cardinals less or equal a.
   Each family of cardinals has an upper bound *)

Definition cardinals_le a:= Zo (osucc a) cardinalp.
Definition cardinals_lt a:= Zo a (fun b => b <c a).

Lemma cardinals_leP a : cardinalp a -> 
  forall b, (inc b (cardinals_le a) <->  (b <=c a)).
Proof. 
move=> ca b; rewrite/cardinals_le; split.
  move /Zo_P => [/(oleP (proj1 ca)) bs cb];exact:(ocle3 cb ca bs). 
move => lba;apply: Zo_i; first by apply /(oleP (proj1 ca))/(ocle lba).
exact: (proj31 lba).
Qed.

Lemma cardinals_ltP a: cardinalp a ->
  (forall b, inc b (cardinals_lt a) <-> (b <c a)).
Proof.
move=> cx y; split; first by  move /Zo_P => [bs cb].
by move => h; move: (oclt h) => /(oltP0) [ _ _ yx]; apply /Zo_i.
Qed.

Lemma cardinals_le_alt a: cardinalp a ->
  (cardinals_le a) = fun_image (\Po a) cardinal.
Proof.
move => h; set_extens t.
  move/(cardinals_leP h) => ha.
  move/cardinal_le_aux1: (ha) => /set_leP [y /setP_P yx /card_eqP exy].
  by apply /funI_P; ex_tac; rewrite - (card_card (proj31 ha)).
move/funI_P => [z /setP_P /sub_smaller ha ->]; apply /(cardinals_leP h).
by rewrite - (card_card h).
Qed.

Lemma CS_sup E: cardinal_set E -> cardinalp (\csup E).
Proof.
move=> alc.
have os: ordinal_set E by move=> t /alc/proj1.
have oe:= (OS_sup os).
apply /cardinalP; split => // z zE /card_eqP ezE.
move/setU_P:zE => [a za ax].
move/cardinalP: (alc _ ax) =>[_ h]; case: (h _ za).
apply/card_eqP; apply:cleA. 
- by move: (sub_smaller (setU_s1 ax)); rewrite ezE.
- exact (sub_smaller (ordinal_transitive (os _ ax) za)).
Qed.

Lemma card_ub_sup E y: cardinalp y -> (forall i, inc i E -> i <=c y) ->
  \csup E <=c y.
Proof.
move => cy ali.
have csE: cardinal_set E by move => i /ali [].
have: (\csup E) <=o y by apply: (ord_ub_sup (proj1 cy)) => o /ali/ocle.
by move /ocle1; rewrite (card_card (CS_sup csE)) (card_card cy).
Qed.


Lemma card_sup_ub E: cardinal_set E ->
  forall i, inc i E -> i <=c \csup E.
Proof.
move => h; move: (CS_sup h) => cs.
have os:= oset_cset h.
move=> i ie; move: (ord_sup_ub os ie)=> [pa pb pc]; split; fprops.
Qed.


Lemma card_sup_image E f g: 
  (forall x, inc x E -> f x <=c g x) -> 
  \csup (fun_image E f) <=c \csup (fun_image E g).
Proof.
move => h.
have pb: cardinal_set (fun_image E g).
  by move => t /funI_P [z zE ->]; case: (h _ zE).
apply: card_ub_sup => //; first by apply: CS_sup.
move=> i /funI_P [z zE ->]; apply: (cleT (h _ zE)).
apply: card_sup_ub => //; apply/funI_P; ex_tac.
Qed.

(* Lemmas cardinal_supremum1 and cardinal_supremum2  moved to ssete11 *)

Lemma surjective_cle x y:
  (exists z, surjection_prop z x y) ->
  y <=cc x.
Proof. 
move=> [z [sjz sz tz]].
apply /eq_subset_cardP1.
move: (exists_right_inv_from_surj sjz) => [f ri].
have ii:=(right_inverse_fi ri).
have si:= (right_i_source ri).
move: ri=> [[_ _ ti] _].
by rewrite -tz - sz - si ti; exists f.
Qed.


Lemma card_le_surj a b : a <=cc b -> nonempty a ->
  exists f, surjection_prop f b a.
Proof. 
move => /eq_subset_cardP1 [f [fi <- tf]] nes.
move: (exists_left_inv_from_inj fi nes) => [g gp]; exists g; hnf.
rewrite (left_i_source gp) (left_i_target gp).
split => //; apply: (left_inverse_fs gp).
Qed.

Lemma image_smaller f: function f -> (Imf f) <=cc (source f).
Proof. 
move=> ff.
apply: surjective_cle. 
exists (restriction_to_image f).
split; rewrite/ restriction_to_image /restriction2; aw; trivial.
exact: (restriction_to_image_fs ff).
Qed.

Lemma image_smaller1 f x: function f -> (Vfs f x) <=cc x.
Proof.
move => pa.
move: (@subsetI2l x (source f)) (@subsetI2r x (source f)) => a1 a2.
have ->: Vfs f x = Vfs f (x \cap (source f)).
   set_extens t => /dirim_P [u p1 p2]; apply /dirim_P; exists u => //.
     apply /setI2_P;split => //; Wtac. 
   by apply: a1.
move: (restriction1_fs pa a2) (sub_smaller a1) => sjb le1.
move: (image_smaller (proj1 sjb)). 
rewrite (surjective_pr0 sjb) /restriction1; aw => le2; apply:cleT le2 le1.
Qed.


Lemma range_smaller f: fgraph f -> (range f) <=cc (domain f).
Proof.
move=> fgf.
have ff: (function (triple (domain f) (range f) f)).
  by apply: function_pr; fprops. 
have ->: (range f = Imf (triple (domain f)(range f) f)). 
  by rewrite (ImfE ff); aw.
by move:(image_smaller ff); aw.
Qed.

Lemma fun_image_smaller a f: (fun_image a f) <=cc a.
Proof.
have sjb: (surjection (Lf f a (fun_image a f))). 
    apply: lf_surjective; first by move=> t ta; apply /funI_P; ex_tac.
    by move=> y /funI_P.
by move: (image_smaller (proj1 sjb)); rewrite (surjective_pr0 sjb); aw.
Qed.

End Cardinal. 
Export Cardinal.
