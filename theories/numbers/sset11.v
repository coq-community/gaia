(** * Theory of Sets : Ordinals
  Copyright INRIA (2009-2013 Apics; Marelle Team (Jose Grimm).
*)
(* $Id: sset11.v,v 1.6 2018/09/04 07:57:59 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Export sset10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals1.

(** ** Sums and products of orders  *)

(** Ordinal sum of a family of orders g indexed by the substrate of r *)

Lemma orprod_wor r g:
  worder_on r (domain g) ->  worder_fam g -> finite_set (substrate r) ->
  worder (order_prod r g). 
Proof.
move=> [wor sr] alw fs.
have lea:orprod_ax r g by split => // i ie; exact (proj1 (alw _ ie)).
move h: (cardinal (substrate r)) => n.
have nN: natp n by apply /NatP; rewrite - h. 
clear wor sr fs; move:n nN r g lea alw h.
apply: Nat_induction.
  move=> r g lea alw cr.
  move:(orprod_osr lea) => [lo].
  rewrite /prod_of_substrates /fam_of_substrates -(proj32 lea).
  rewrite  (card_nonempty cr) setXb_0' => s1.
  exact:(worder_set1 (conj lo s1)).
move=> n nN hrec r g lea alwo csr.
have lo: (order (order_prod r g)) by fprops.  
have [[or _] sr alo] := lea.
apply:(worder_prop_rev lo) => [x xsr [x0 x0x]].
move: xsr;rewrite orprod_sr // => xsr. 
case: (emptyset_dichot (substrate r)) => nesr.
  by case: (@succ_nz n); rewrite - csr nesr cardinal_set0.
move: (worder_least (proj31 lea) nesr) => [i []]; rewrite {1} sr => isr ilsr.
set Y := fun_image x (fun z => Vg z i).
have sYs: (sub Y (substrate (Vg g i))). 
  move=> t /funI_P [z zx ->]; apply: prod_of_substrates_p; fprops.
have neY: (nonempty Y) by exists (Vg x0 i); apply /funI_P; ex_tac.
move: (worder_prop (alwo _ isr) sYs neY) => [z zY zl].
move: (proj1 (alwo _ isr)) => or'.
set X1 := Zo x (fun t => Vg t i = z).
have p1: (forall a b, inc a x -> inc b x -> inc a X1 -> ~ inc b X1 ->
    glt (order_prod r g) a b).
  move=> a b ax bx aX1 bX1; split; last by dneg ab; rewrite -ab.
  apply orprod_gleP =>//; split;fprops. 
  right; exists i; split => //; first by ue. 
    have ib: z <> Vg b i by move=> eq2; move: bX1 => /Zo_P; apply;split => //.
    have vbY: (inc (Vg b i) Y) by apply /funI_P; ex_tac.
    move: aX1 => /Zo_P [_ ->]; split => //; apply: (zl  _ vbY).
  move=> j rj.
  have jsr:  (inc j (substrate r)) by order_tac.
  move: (ilsr _ jsr) => le2; order_tac. 
set I1 := (substrate r) -s1 i.
set r1 := induced_order r I1.
set g1 := restr g I1.
have I1sr: (sub I1 (substrate r)) by  apply: sub_setC.
have hh: sub I1 (domain g) by ue.
have dg1: domain g1 = I1 by rewrite /g1;aw; trivial; ue.
have sdg1g: sub (domain g1) (domain g) by rewrite dg1; ue.
have la1: orprod_ax r1 g1.
  split => //. 
  + move: lea => [WO _ _]; apply: induced_wor => //.
  + by rewrite /r1 iorder_sr.
  + hnf; rewrite /g1 => j j1; move: (alo _ (sdg1g _ j1)) => og1.
    by rewrite LgV//; ue.
have alw: allf g1 worder.
  move=>j jdg; rewrite /g1 restr_ev; [by apply: alwo;apply: sdg1g| ue].
have cs: cardinal (substrate r1) = n.
  rewrite - sr in isr.
  rewrite /r1 /I1 iorder_sr // - cpred_pr5 // csr cpred_pr1; fprops.
set X2 := fun_image X1 (fun z => restr z I1).
have X2s: sub X2 (substrate (order_prod r1 g1)).
  rewrite orprod_sr//; move=> t /funI_P [u uX1 ->]; apply /setXb_P.
  have ux:  (inc u x) by move: uX1=> /Zo_S.
  move: (xsr _ ux) => /prod_of_substratesP [fgfu du iVV].
  aw;rewrite /g1 Lgd; split;fprops; move => j jI1; rewrite !LgV// ? Lgd//.
  apply: iVV; ue.
have neX2: (nonempty X2).
  apply: funI_setne; move: zY => /funI_P [z0 z0x pz0];exists z0.
  by apply /Zo_P. 
move:(worder_prop (hrec _ _ la1 alw cs) X2s neX2)=> [w /funI_P [v vX1 rv] wle].
have vx: inc v x by move: vX1 => /Zo_S. 
have sxs: sub x (substrate (order_prod r g)) by rewrite orprod_sr.
ex_tac.
move=> u ux1.
case: (equal_or_not (Vg u i) z)=> Vu; last first. 
  have nv: (~ inc u X1) by move /Zo_P => [_]. 
  by move: (p1 _ _ vx ux1 vX1 nv)=> [le _]. 
have uX1: (inc u X1) by apply: Zo_i.
have rX2: (inc (restr u I1) X2) by apply /funI_P; ex_tac.
move: (wle _ rX2).
move /(orprod_gle1P la1) => [wp rp]; set T:= Zo _ _ => op.
apply /(orprod_gle1P lea); split;fprops.
have aa:sub (Zo (domain g) (fun i0 => Vg v i0 <> Vg u i0)) (substrate r).
  by rewrite sr; apply: Zo_S.
move=> j []; rewrite (iorder_sr or aa) => /Zo_P [jd  nsv] aux.
have jI1: inc j I1.
  by apply /setC1_P;split => //; 
    [ ue | dneg ij; rewrite ij Vu; move:vX1 => /Zo_P []]. 
move/prod_of_substratesP: (xsr _ vx) =>  [fgv dv vp].
move /prod_of_substratesP: (xsr _ ux1) => [fgu du up].
have pa: sub I1 (domain u) by rewrite du -dg1.
have pb: sub I1 (domain v) by rewrite dv -dg1.
have jT: inc j T by  apply: Zo_i; [ue | rewrite rv !LgV].
have lej: (least (induced_order r1 T) j).
  move: (iorder_osr or I1sr) => [or1' sr1']. 
  have sT: sub T (substrate r1) by rewrite /r1 iorder_sr // -dg1;apply: Zo_S.
  hnf;rewrite iorder_sr //; split =>// x1 aux2.
  move: (aux2) => /Zo_P []; rewrite dg1 => xi; rewrite rv !LgV// => pc.
  apply /(iorder_gle0P _  jT aux2); apply /(iorder_gle0P _ jI1 xi).
  have aux3: (inc x1 (Zo (domain g) (fun i => Vg v i <> Vg u i))).
     apply: Zo_i => //; ue.
  exact: (iorder_gle1 (aux _ aux3)).  
by move: (op _ lej); rewrite rv /g1 !LgV.
Qed.

Lemma orprod2_wor r r':
  worder r -> worder r' -> worder (order_prod2 r r').
Proof. 
move: cdo_wor => [pa pb] wor wor'; apply: orprod_wor => //.
- saw.
- by hnf; aw; move=> i ind; try_lvariant ind.
- apply: finite_set_scdo.
Qed.

Lemma orsum2_wor r r':
  worder r -> worder r' -> worder (order_sum2 r r').
Proof. 
move: cdo_wor => [pa pb] wor wor'; apply: orsum_wor; first by aw.
by hnf;aw;move=> i ind; try_lvariant ind.
Qed.

Hint Resolve  orsum2_wor orprod2_wor: fprops.

Lemma set_ord_lt_prop3a a: ordinalp a -> ole_on a = ordinal_o a.
Proof.
move => oa.
have [p2 p1]:= (wordering_ole_pr (Os_ordinal oa)).
apply: sgraph_exten; try apply: order_is_graph; fprops.
move => u v; split; move /graph_on_P1=> [pa pb pc]; 
    apply /graph_on_P1 => //;split => //.
+ by case: pc.
+ split; [ exact:(Os_ordinal oa pa) | exact: (Os_ordinal oa pb) | done].
Qed.

Lemma set_ord_lt_prop3 a: ordinalp a -> ordinal (ole_on a) = a.
Proof.
move=> oa; rewrite (set_ord_lt_prop3a oa); apply: (ordinal_o_o oa).
Qed.

Lemma finite_ordinal1 n: natp n -> ordinal (Nint_co n) = n.
Proof.
move=> nN. 
have cn: cardinalp n by fprops.
have ox: ordinalp n by apply: OS_cardinal.
have cnn: cardinal n = n by apply: card_card.
have fs: finite_set n by apply /NatP; ue.
have w1 := (Nintco_wor n).
have on := (OS_ordinal (proj1 w1)).
have p1 := (worder_total (ordinal_o_wor ox)).
have p2 := (worder_total (ordinal_o_wor on)).
have pa := (ordinal_o_sr n).
have [f [_ _ [bf sf tf] _]]:= (ordinal_o_is (proj1 w1)).
have : (source f) \Eq (target f) by exists f;split => //.
rewrite tf sf (proj2 w1).
set S := substrate _ => /card_eqP aux.
have p3: substrate (ordinal_o n) \Eq S.
   by apply/card_eqP; rewrite pa - aux card_Nint.
have fs1: finite_set (substrate (ordinal_o n)) by rewrite (ordinal_o_sr n).
have [g [fiso _]] := (isomorphism_worder_finite p1 p2 fs1 p3).
by symmetry;apply: (ordinal_o_isu ox on); exists g.
Qed.

Lemma ord_omega_pr: ordinal Nat_order = omega0.
Proof.
have bwo := proj1 Nat_order_wor.
suff: (ordinal_o omega0 = Nat_order).
  by move => <-; apply: ordinal_o_o; fprops.
apply: order_exten;fprops. 
move => u v; split.
  move /graph_on_P1 => [p1 p2 p3]; apply Nat_order_leP.
  by split => //;split; fprops.
by move/Nat_order_leP => [pa pb [_ _ pc]];apply /graph_on_P1.
Qed.

Lemma olt_0omega: \0o <o omega0.
Proof. apply /olt_omegaP; apply: NS0. Qed.

Lemma omega_nz: omega0 <> \0o.
Proof. exact (nesym (proj2 olt_0omega)). Qed.

Lemma olt_1omega: \1o <o omega0.
Proof. apply /olt_omegaP; apply: NS1. Qed.

Lemma ole_2omega: \2o <=o omega0.
Proof. by  move: NS2 => /olt_omegaP; case. Qed.

Lemma olt_2omega: \2o <o omega0.
Proof. apply /olt_omegaP; apply: NS2. Qed.

(** Properties of zero *)

Lemma ordinal_o_set0: ordinal_o emptyset = emptyset.
Proof. by apply: empty_substrate_zero; rewrite ordinal_o_sr. Qed.

Lemma ordinal0_pr: ordinal emptyset = \0o.
Proof. rewrite - ordinal_o_set0; exact (ordinal_o_o OS0). Qed.

Lemma ordinal0_pr1 r: substrate r = emptyset -> ordinal r = \0o.
Proof. move => sx;rewrite (empty_substrate_zero sx) ordinal0_pr //. Qed.

Lemma ordinal0_pr2 r: worder r -> ordinal r = \0o -> substrate r = emptyset.
Proof.
move=> /ordinal_o_is ha hb.
move: ha; rewrite hb => [] [f [_ _ [bf sf tf] _]].
rewrite (ordinal_o_sr \0o) /ord_zero in tf; rewrite - sf.
apply /set0_P => y ysf; empty_tac1 (Vf f y); Wtac; fct_tac.
Qed.

Lemma osucc_nz x : osucc x <> \0o.
Proof. by move => h; move: (succ_i x); rewrite h => /in_set0. Qed.

Lemma ordinal1_pr x: ordinal (singleton (J x x)) = \1o.
Proof.
have [p1 p2]:= (set1_wor x).
apply: (ordinal_o_isu2 p1 OS1); apply: set1_order_is2; fprops.
  by rewrite p2; exists x.
by rewrite ordinal_o_sr; exists emptyset.
Qed.

Lemma set1_ordinal r: order r -> singletonp (substrate r) ->
  ordinal r = \1o.
Proof.
move=> ox sx; move: (set1_order_is1 ox sx) => [y ->]; exact:ordinal1_pr.
Qed.

(** ** ordinal sum and product *)


Definition osum r g :=  
   ordinal (order_sum r (Lgcomp g  ordinal_o)).
Definition oprod r g := 
   ordinal (order_prod r (Lgcomp g ordinal_o)).
Definition osum2 a b := ordinal (order_sum2 (ordinal_o a) (ordinal_o b)).
Definition oprod2 a b := ordinal (order_prod2 (ordinal_o a) (ordinal_o b)).

Notation "a +o b" := (osum2 a b) (at level 50).
Notation "a *o b" := (oprod2 a b) (at level 40).

Lemma OS_sum r g: worder_on r (domain g) -> ordinal_fam g ->
  ordinalp (osum r g).
Proof.
move=> [or sr] alo ; apply: OS_ordinal.
apply: orsum_wor; [ saw | hnf; aw => i idg; rewrite LgV //; fprops].
Qed.

Lemma OS_prod r g: worder_on r (domain g) -> ordinal_fam g -> 
  finite_set (substrate r) -> ordinalp (oprod r g).
Proof. 
move=> osr alo fs; apply: OS_ordinal.
apply: orprod_wor => //; [ by aw|  hnf; aw=> i idg; rewrite LgV//; fprops ].
Qed.

Lemma osum2_rw a b:
   a +o b = osum canonical_doubleton_order (variantLc a b).
Proof. by rewrite /osum2 /osum /order_sum2 variantLc_comp. Qed.

Lemma oprod2_rw a b:
  a *o b = oprod canonical_doubleton_order (variantLc b a).
Proof. by rewrite /oprod2 /oprod /order_prod2 variantLc_comp. Qed.


Lemma OS_sum2 a b: ordinalp a -> ordinalp b -> ordinalp (a +o b).
Proof.  move=> wo1 wo2;apply: OS_ordinal; fprops. Qed.

Lemma OS_prod2 a b: ordinalp a -> ordinalp b -> ordinalp (a *o b).
Proof. 
move=> wo1 wo2; apply: OS_ordinal; fprops.
Qed.

Hint Resolve OS_sum2 OS_prod2 : fprops.

Lemma orsum_invariant1 r r' f g g':
  order_on r (domain g) -> 
  order_on r' (domain g') -> 
  order_isomorphism f r r' ->
  (forall i, inc i (substrate r) ->  (Vg g i) \Is  (Vg g' (Vf f i))) ->
  (order_sum r g) \Is (order_sum r' g').
Proof. 
move=> [or sr] [or' sr'] oi ali.
have oa: (orsum_ax r g).
  by split => //; hnf;rewrite - sr=> i idg; move:(ali _ idg)=> [h []].
move: (oi) => [_ _ [[[ff ijf] sjf] srf tgf] oif].
have oa': orsum_ax r' g'. 
  split => //; hnf;rewrite - sr' - tgf=> i idg.
  move: ((proj2 sjf) _ idg) => [x xsf ->].
  by rewrite srf in xsf; move: (ali _ xsf)=> [h [o1 o2 _]].
move: (orsum_or oa) (orsum_or oa') => h1 h2; aw.
set fa := fam_of_substrates g. 
set fb := fam_of_substrates g'.
pose oj i := choose (fun z => order_isomorphism z (Vg g i) (Vg g' (Vf f i))).
have ojp: (forall i, inc i (substrate r) -> 
    order_isomorphism (oj i) (Vg g i) (Vg g' (Vf f i))).
  move=> i isr; rewrite /oj; apply: (choose_pr  (ali _ isr)).
pose h x := J (Vf (oj (Q x))  (P x))  (Vf f (Q x)).
have ta: (forall x, inc x (disjointU fa) -> inc (h x) (disjointU fb)).
  move=> x xd; case: (disjointU_hi xd); rewrite /fa/fam_of_substrates. 
  rewrite Lgd => qd; rewrite LgV // => ps px.
  have wq: (inc (Vf f (Q x)) (domain g')). 
    by rewrite - sr' - tgf; Wtac; rewrite  srf sr.
  apply: disjointU_pi; rewrite /fb ? fos_d // LgV //.
  rewrite sr in ojp;move: (ojp  _ qd) => [_ _ [fx sx tx] _].
  by rewrite - tx; Wtac; fct_tac.
have ta1: lf_axiom h (substrate (order_sum r g)) (substrate(order_sum r' g')). 
  by rewrite !orsum_sr. 
exists (Lf h (substrate (order_sum r g)) (substrate (order_sum r' g'))).
hnf; rewrite /bijection_prop lf_source lf_target; split => //.
  rewrite !orsum_sr //; split=> //; apply: lf_bijective =>//.
    rewrite /h => u v us vs eq. 
    move:(du_index_pr1 us) (du_index_pr1 vs)=> [Qu Pu pu][Qv Pv pv].
    move: (pr2_def eq) (pr1_def eq) => r1 r2.
    have sQ: Q u = Q v by apply: ijf => //; rewrite srf;ue.
    rewrite - sQ in r2 Pv; rewrite - sr in  Qu.
    move: (ojp _ Qu) => [_ _ [[[_ ijfj] _] sfj _] _].
    apply: pair_exten =>//; apply: ijfj =>//; ue.
  move=> y ys; move:  (du_index_pr1 ys)=> [Qy Py py].
  rewrite - sr' -tgf in Qy; move:((proj2 sjf) _ Qy) =>[x xsf Wx].
  rewrite srf in xsf; move: (ojp  _ xsf) => [_ _ [[_ sjj] sfj tjj] _].
  rewrite Wx - tjj in Py; move: ((proj2 sjj) _ Py)=> [x0 x0s x0w].
  have xdg: inc x (domain g) by ue.
  exists (J x0 x).
    apply: disjointU_pi; aw; trivial;rewrite LgV //; ue.
  by rewrite /h; aw; rewrite -Wx -x0w; aw; rewrite py.
hnf;aw; rewrite !orsum_sr // => x y xs ys; rewrite !LfV//.
move: ta1; rewrite ! orsum_sr // => ta2; move: (ta2 _ xs)(ta2 _ ys) => ha hb.
move: (du_index_pr1 xs) (du_index_pr1 ys) => [Qx Px px][Qy Py py].
rewrite - sr - srf in Qx Qy; rewrite - srf in ojp.
move: (ojp _ Qx) =>  [_ _ [_ sfj _] ojj].
have qa: inc (P x) (source (oj (Q x))) by ue.
have qb: Q x = Q y -> inc (P y) (source (oj (Q x))) by rewrite  sfj => ->.
split; move/orsum_gleP => [_ _ aux]; apply /orsum_gleP;split => //; move: aux;
  rewrite /order_sum_r /h !pr1_pair !pr2_pair.
  case => pa; first by left; apply /(order_isomorphism_siso oi Qx Qy).
  move: pa => [pa pb];rewrite - pa; right; split => //.
  by apply/ojj => //; apply: qb.
case => pa; first by left; apply /(order_isomorphism_siso oi Qx Qy).
move: pa => [pa]; move:  (ijf _ _ Qx Qy pa) => pc; rewrite - pc => pb.
by right;split => //; apply /ojj => //; apply: qb.
Qed.

Lemma orsum_invariant2 r g g':
  order r -> substrate r = domain g ->
  substrate r = domain g' ->
  (forall i, inc i (substrate r) -> (Vg g i) \Is (Vg g' i)) ->
  (order_sum r g) \Is (order_sum r g').
Proof.
move=> or sr sr' ai.
apply: (orsum_invariant1 (conj or sr) (conj or sr') (identity_is or)).
move => i isr; rewrite idV //; apply: ai =>//.
Qed.

Lemma orsum_invariant3 r g:
  worder_on r (domain g) -> worder_fam g ->
  ordinal (order_sum r g) = 
    osum r (Lg (substrate r) (fun i => ordinal (Vg g i))).
Proof.
move => [wor sr] alo.
have or: order r by fprops.
apply: ordinal_o_isu1.
- by apply: orsum_wor.
- apply: orsum_wor; [ by aw | hnf; aw  => i isr; rewrite !LgV//; aw; trivial].
  by rewrite sr in isr; apply: (ordinal_o_wor (OS_ordinal (alo _ isr))).
- apply: orsum_invariant2 => //; aw; trivial.
  rewrite sr => i isr; rewrite !LgV //; last  by aw.
  apply: (ordinal_o_is (alo _ isr)).
Qed.

Lemma orsum_invariant4 r1 r2 r3 r4:
  r1 \Is r3 -> r2 \Is r4 ->
  (order_sum2 r1 r2) \Is (order_sum2 r3 r4).
Proof.
move=> h1 h2; rewrite /order_sum2.
move: cdo_wor => [[res _] sr].
apply: orsum_invariant2; rewrite ?sr;aww.
by move=> i itp; try_lvariant itp.
Qed.

Lemma orprod_invariant1 r r' f g g':
  worder_on r (domain g) -> 
  order_on r' (domain g') -> 
  order_isomorphism f r r' ->
  (forall i, inc i (substrate r) -> (Vg g i) \Is (Vg g'  (Vf f i))) ->
  (order_prod r g) \Is (order_prod r' g').
Proof. 
move=> [wor sr] [or' sr'] oif ali. 
have aux: (r \Is r') by exists f. 
have wor':= (worder_invariance aux wor). 
clear aux.
have bf: bijection f by move: oif => [_ _ [bf _ _] _].
move: (oif) => [or _ [[[ff ijf] sjf] srf tgf] oif'].
have oa: (orprod_ax r g).
  by split => //;hnf;rewrite - sr=> i idg; move:(ali _ idg)=> [h [o1 o2 _]].
have oa': orprod_ax r' g'.
  split => //;hnf;rewrite - sr' - tgf => i idg.
  move: ((proj2 sjf) _ idg) => [x xsf ->].
  by rewrite srf in xsf; move: (ali _ xsf)=> [h [o1 o2 _]].
move: (orprod_or oa)(orprod_or oa') => o1 o2; aw.
set fa := fam_of_substrates g. 
set fb := fam_of_substrates g'.
pose oi i := choose (fun z => order_isomorphism z (Vg g i) (Vg g' (Vf f i))).
have oip: (forall i, inc i (substrate r) -> 
    order_isomorphism (oi i) (Vg g i) (Vg g' (Vf f i))).
  by move=> i isr; apply: (choose_pr (ali  _ isr)). 
pose fi := Vf (inverse_fun f).
have fip: (forall i, inc i (substrate r') ->  Vf f (fi i) = i).
   move=> i isr; rewrite inverse_V //; ue.
have fis: (forall i, inc i (substrate r') -> inc (fi i) (substrate r)).
  rewrite - tgf - srf; move=> i isf; apply:inverse_Vis =>//.
pose fj :=  Vf f.
have fjs: forall i, inc i (substrate r) -> (inc (fj i) (substrate r')). 
   rewrite - srf - tgf /fj; move=> i isg; fprops. 
have fij: forall i, inc i (substrate r) -> fi (fj i)  = i. 
  rewrite - srf /fi/fj;move => i idf; rewrite inverse_V2 //.
pose h z := Lg (substrate r') (fun i => Vf (oi (fi i))(Vg z (fi i)) ).
set (A := substrate(order_prod r g)).
set (B := substrate(order_prod r' g')).
have HA : A = (prod_of_substrates g) by rewrite /A orprod_sr.
have HB : B = (prod_of_substrates g') by rewrite /B orprod_sr.
have ta: (forall z, inc z A -> inc (h z) B). 
  rewrite HA HB => z /prod_of_substratesP [fgf dz iVV].
  apply /prod_of_substratesP; rewrite /h;split => //; [fprops | by aw | ].
  rewrite - sr' => i isr; rewrite LgV//.
  have fisr:= (fis _ isr).
  move: (oip _ fisr) => [_ _ [boi soi]].
  rewrite  (fip _ isr) => <- _; Wtac; try fct_tac. 
  by rewrite soi; apply: iVV; rewrite - sr.
have ta': (forall w, inc w B -> exists2 z, inc z A & w = h z).
  rewrite HA HB; move => w /prod_of_substratesP [fgf dz iVV].
  exists (Lg (substrate r) (fun i => Vf (inverse_fun (oi i))(Vg w (fj i)))).
    apply /prod_of_substratesP;split => //; [ fprops | by aw | ]. 
    rewrite - sr => i isr; rewrite LgV//.
    move: (oip _ isr) =>  [_ _ [boi soi toi] _ ].
    rewrite - soi; apply: inverse_Vis =>//; rewrite toi.
    apply: iVV; rewrite - sr'; apply: (fjs _ isr).
  rewrite /h; apply: fgraph_exten; [ exact | fprops | by aw ; ue | ].
  rewrite dz - sr'; move=> x xdw /=; move: (fis _ xdw) => fisr.
  rewrite !LgV //; move: (oip _ fisr) =>  [_ _ [boi soi toi] _ ].
  rewrite /fj (fip _ xdw) inverse_V // toi (fip _ xdw); apply: iVV; ue.
have hi: (forall z z', inc z A -> inc z' A -> h z = h z' -> z = z').
  rewrite HA => z z' zA zA' p3; apply: (setXb_exten zA zA').
  hnf; aw;move=> i idg; move: (prod_of_substrates_p zA idg) =>p4.
  have p5 := (prod_of_substrates_p zA' idg).
  rewrite - sr in idg; move: (fij _ idg)(fjs _ idg)  => p6 p7.
  move: (f_equal (Vg ^~(fj i)) p3); rewrite /h !LgV // p6.
  move: (oip _ idg) =>  [_ _ [[[_ ioi] _] soi toi] _ ].
  apply: ioi; ue. 
have ta2: (lf_axiom h A B) by [].
exists (Lf h A B). 
split => //; [ by saw;apply: lf_bijective | hnf; aw].
move=> x y xA yA; rewrite !LfV //; split.
  move /(orprod_gleP oa) => [_ _ ha]; apply /(orprod_gleP oa'). 
  rewrite -HB; split => //; try apply: ta =>//; case:ha => ha.
     by left; rewrite ha.
  move: ha => [j [jst jlt ieq]]; right.
  move: (fjs _ jst)(fij _ jst) => fjst fijt; rewrite /h;ex_tac.
    by rewrite !LgV// fijt; apply: (order_isomorphism_sincr (oip _ jst)).   
  move=> i ifj.
  have isr: inc i (substrate r') by order_tac.
  rewrite !LgV // (ieq (fi i)) // - fijt; apply /(order_isomorphism_siso oif);
    [by rewrite srf; apply: fis  | ue | rewrite ! fip //].
move /(orprod_gleP oa') => [_ _ ha]; apply /(orprod_gleP oa). 
rewrite - HA;split => //.
case:ha=> aux; first by left; apply: hi.
right; move: aux => [j [jsr jlt jle]].
move: (fip _ jsr)(fis _ jsr) => fipa fisa.
ex_tac.
  move:  (oip _ fisa) =>  [_ _ [_ soi toi] _ ].
  apply /(order_isomorphism_siso (oip _ fisa));
   try (rewrite soi; apply: prod_of_substrates_p; ue);
   move: jlt; rewrite /h fipa; rewrite !LgV //.
move=> i lti.
have isr: inc i (substrate r) by order_tac.
move: (isr) => isr1.
move: (oip _ isr) =>  [_ _ [[[_ ioi] _] soi toi] _ ].
apply: ioi.
    move: xA isr; rewrite soi sr HA; apply: prod_of_substrates_p.
  move: yA isr; rewrite soi sr HA; apply: prod_of_substrates_p.
rewrite - srf in isr fisa.
move /(order_isomorphism_siso oif isr fisa): lti; rewrite fip // => aux.
by move: (jle _ aux); rewrite /h ! LgV//; try order_tac; rewrite fij //.
Qed.


Lemma orprod_invariant2 r g g':
  worder r -> substrate r = domain g ->
  substrate r = domain g' -> 
  (forall i, inc i (substrate r) -> (Vg g i) \Is (Vg g' i)) ->
  (order_prod r g) \Is (order_prod r g').
Proof. 
move=> wor sr sr' alo.
have or:=proj1 wor.
apply: (orprod_invariant1 (conj wor sr) (conj or sr') (identity_is or)).
by move=> i isr; rewrite idV //; apply: alo.
Qed.

Lemma orprod_invariant3 r g:
  worder_on r (domain g) -> worder_fam g ->
  finite_set (substrate r) ->
  ordinal (order_prod r g) =
    oprod r (Lg (substrate r) (fun i => ordinal (Vg g i))).
Proof. 
move => [wor sr] alo fsr.
have or:= proj1 wor.
apply: ordinal_o_isu1; first by apply: orprod_wor.
  apply: orprod_wor; aw => //. 
  hnf; rewrite !Lgd; move=> i isr; rewrite !LgV // ? Lgd//.
  rewrite sr in isr; apply: (ordinal_o_wor (OS_ordinal (alo _ isr))).
apply: orprod_invariant2 => //; first by aw.
rewrite sr;move=> i isr; rewrite !LgV // ? Lgd //.
apply: (ordinal_o_is  (alo _ isr)).
Qed.

Lemma orprod_invariant4 r1 r2 r3 r4:
  r1 \Is r3 -> r2 \Is r4 ->
  (order_prod2 r1 r2) \Is (order_prod2 r3 r4).
Proof.
move=> h1 h2; rewrite /order_prod2.
move:cdo_wor => [pa pb].
by apply: orprod_invariant2; rewrite ? pb ? Lgd // => i itp; try_lvariant itp.
Qed.

Lemma orsum_invariant5 r1 r2 r3: worder r1 -> worder r2 ->
  (order_sum2 r1 r2) \Is r3 ->
  (ordinal r1) +o (ordinal r2) = ordinal r3.
Proof.
move=> oa ob h. 
rewrite /osum2; apply: ordinal_o_isu1.
  apply: orsum2_wor.
    apply: (ordinal_o_wor (OS_ordinal oa)).
    apply: (ordinal_o_wor (OS_ordinal ob)).
  move: h (orsum2_wor oa ob); apply:  worder_invariance.
apply: orderIT h; apply: orsum_invariant4.
  apply: orderIS; apply: (ordinal_o_is oa).
apply: orderIS;  apply: (ordinal_o_is ob).
Qed.

Lemma orprod_invariant5 r1 r2 r3: worder r1 -> worder r2 ->
  (order_prod2 r1 r2) \Is r3 ->
  (ordinal r1) *o (ordinal r2) = ordinal r3.
Proof.
move=> oa ob  h. 
rewrite /oprod2; apply: ordinal_o_isu1.
  apply: orprod2_wor.
    apply: (ordinal_o_wor (OS_ordinal oa)).
    apply: (ordinal_o_wor (OS_ordinal ob)).
  move: h (orprod2_wor oa ob); apply:  worder_invariance.
apply: orderIT h; apply: orprod_invariant4.
  apply: orderIS; apply: (ordinal_o_is oa).
apply: orderIS;  apply: (ordinal_o_is ob).
Qed.

Lemma oprod_pr1 a b r:
  ordinalp a -> ordinalp b -> (ordinal_o b) \Is r ->
  a *o b = osum r (cst_graph (substrate r) a).
Proof. 
move=> ota otb ibr.
have wo0:= (ordinal_o_wor ota).
have wo1 := (ordinal_o_wor otb).
have wo2:= (worder_invariance ibr wo1).
rewrite /oprod2 /osum {1} /cst_graph.
apply: ordinal_o_isu1.
    by apply: orprod2_wor; apply: ordinal_o_wor.
  apply: orsum_wor; first by aw. 
  hnf; aw => i iser; rewrite !LgV //? Lgd //.
apply: (orderIT (order_prod_pr (worder_or wo0)(worder_or wo1))).
have [f isf] := ibr.
rewrite /cst_graph; apply: (@orsum_invariant1 _ _ f); aw; trivial. 
- rewrite ordinal_o_sr; apply: sub_osr. 
- split; fprops.
move: isf => [_ _ [[[ff _] _] <- tf] _] i id.
move: (Vf_target ff id); rewrite tf=> vt; rewrite !LgV// ? Lgd //.
apply: orderIR; fprops.
Qed.

Lemma osum_set0 r g: domain g = emptyset -> osum r g = \0o.
Proof. 
move=> dge.
rewrite /osum /Lgcomp dge /Lg funI_set0 /order_sum ; set r' := graph_on _ _.
suff: r' = emptyset by move => ->; exact ordinal0_pr.
apply/set0_P => t /Zo_S /setX_P [_ _] /du_index_pr1; rewrite domain_set0.
by move => [/in_set0].
Qed.

Lemma Zo_empty f: Zo emptyset f = emptyset.
Proof. by apply/set0_P => t /Zo_S /in_set0. Qed.


Lemma oprod_set0 r g:  domain g = emptyset ->  oprod r g = \1o.
Proof. 
move=> dge.
rewrite/oprod/Lgcomp dge /Lg funI_set0/order_prod /graph_on.
have [y ->]: singletonp (prod_of_substrates emptyset).
  by apply: setX_set1; hnf;rewrite /fam_of_substrates; aw => t/in_set0.
set s1 := Zo _ _. 
suff: s1 = singleton (J y y) by move => ->; exact:ordinal1_pr.
apply:set1_pr.
  apply: Zo_i; first by apply: setXp_i; apply /set1_P.
  move => j []; rewrite domain_set0 Zo_empty induced_order_empty.
  by rewrite (proj2 set0_wor) => /in_set0.
by move => z /Zo_S /setX_P [pz /set1_P pa /set1_P pb]; rewrite - pz pa pb.
Qed.
  
Lemma osum_set1 r g i:
  order_on r (domain g) -> 
  substrate r = singleton i -> ordinalp (Vg g i) ->
  osum r g = Vg g i.
Proof. 
move=> [or sr] srs otve.
have dgi: domain g = singleton i by rewrite - sr srs.
have idg: inc i (domain g) by rewrite dgi; fprops.
have wor:= (worder_set1 (conj or srs)).
have ove:= (ordinal_o_wor otve).
rewrite /osum /Lgcomp. 
set g' := Lg _ _.
have osa: orsum_ax r g'.
   rewrite /g'; hnf; saw => //;hnf; aw.
   rewrite dgi => j /set1_P ->; rewrite LgV// ; fprops.
have wos: worder (order_sum r g').
  rewrite/g';apply: orsum_wor; first by saw.
  hnf; rewrite Lgd dgi; move=> j /set1_P ->; rewrite LgV //; fprops.
apply: (ordinal_o_isu2 wos otve).
set (E:= substrate (order_sum r g')); set (F := substrate (ordinal_o (Vg g i))).
have He:E =sum_of_substrates g' by rewrite /E orsum_sr //.
have Hf:F = Vg g i by apply: (ordinal_o_sr).
have uE: (forall u, inc u E <-> [/\ pairp u, Q u = i &inc (P u) F]).
  move=> u; rewrite He /g';  split.
    move=> us; move: (du_index_pr1 us) => [].
    rewrite Lgd; move=> Qu; rewrite LgV //.
    move: Qu; rewrite dgi=> /set1_P -> pa pb; split => //; ue.
  move => [pu Qu Pu]; rewrite - pu Qu; apply: disjointU_pi; aw; trivial.
  by rewrite ! LgV//; aw.
have ta: (lf_axiom P E F) by move=> t /uE [_].
exists (Lf P E F).
split; fprops; first (hnf;saw).
  apply: lf_bijective => //. 
    move=> u v  =>/uE [pu Qu Pu] /uE [pv Qv Pv] sp.
    apply: pair_exten =>//; ue.
  move=> y ys; exists (J y i); aw => //; apply /uE; saw;fprops.
hnf; aw => a b aE bE; rewrite !LfV //.
move: (aE)(bE) => /uE  [pu Qu Pu] /uE [pv Qv Pv].
have aux: inc (Q a) (domain g) by rewrite dgi Qu ; fprops.
have <-: (Vg g' (Q a)) = ordinal_o (Vg g i) by  rewrite /g' LgV// Qu.
split.
   by move /orsum_gleP => [_ _]; case; move => [_] //; rewrite Qu Qv.
move => h; apply /orsum_gleP;split; rewrite - ? He //; right;split => //; ue.
Qed.

Lemma oprod_set1 r g i:
  order_on r (domain g) ->
  substrate r = singleton i ->  ordinalp (Vg g i) ->
  oprod r g = Vg g i.
Proof. 
move=> [or sr] srs otvi.
have wor :=(worder_set1 (conj or srs)).
have dgi: domain g = singleton i by  rewrite - sr srs.
have idg: (inc i (domain g)) by rewrite dgi; fprops.
have ovi:= (ordinal_o_wor otvi).
rewrite /oprod /Lgcomp. 
set g' := Lg _ _.
have la: (orprod_ax r g').
  rewrite /g'; split => //; first by aw; ue.
  hnf; aw; move=> j; rewrite dgi=> id; rewrite LgV //; fprops.
have ora := (orprod_or la).
have wos: worder(order_prod r g').
  rewrite/g';apply: orprod_wor=> //; first by saw.
    hnf;  aw; rewrite dgi; move=> j /set1_P ->; rewrite LgV //; fprops.
  rewrite srs; apply: set1_finite.
apply: (ordinal_o_isu2 wos otvi).
move: (orprod_sr la).
set E := substrate (order_prod r g').
set F := substrate (ordinal_o (Vg g i)).
have Hf: F = Vg g i by rewrite /F; apply: ordinal_o_sr.
have Hf': F = substrate (Vg g' i) by rewrite /g' LgV.
move=> slo; move: (slo).
rewrite /prod_of_substrates/fam_of_substrates=> slo'.
have dg: domain g' = singleton i by rewrite /g' Lgd.
have ig: inc i (domain g') by rewrite dg; fprops.
have ta: lf_axiom (Vg ^~  i) E F.
  move=> t te; move: te ig; rewrite slo  Hf'; apply: prod_of_substrates_p.
have Hc:forall a b, inc a E-> inc b E -> Vg a i = Vg b i -> a = b.
  move=> a b; rewrite slo' dg => aE bE sV.
  by apply: (setXb_exten aE bE); aw; move=> j /set1_P ->.
exists (Lf (Vg ^~i) E F).
hnf;rewrite /bijection_prop lf_source lf_target; split;fprops.
  saw;apply: lf_bijective =>//.
  move=> y ys; exists (cst_graph (singleton i) y); last by rewrite LgV//;fprops.
  rewrite slo' dg; apply /setXb_P; fprops;split;aww.
  by move=> j /set1_P ->; rewrite !LgV//; fprops; rewrite - Hf'.
hnf; aw; move=> a b aE bE; rewrite !LfV //.
have qa: fgraph (Lg (domain g') (fun j => substrate (Vg j g'))) by fprops.
have aux: (ordinal_o (Vg g i)) = Vg g' i by rewrite /g' LgV.
split.
   move/(orprod_gleP la) => [_ _]; case.
     have orve:= (worder_or ovi).
     move=> ->; order_tac.
     move: bE; rewrite slo'; move /setXb_P=> [fgb db]; rewrite - db => aa.
     have ed: inc i (domain b) by rewrite db dg Lgd; fprops.
     move: (aa _ ed); rewrite !LgV //. 
  rewrite sr dgi;move=> [j [jsr]]; move /set1_P: (jsr) => <-.
  by move => [jle _] _; move: jle; rewrite /g' LgV // dgi.
move=> h; apply /(orprod_gleP la); rewrite - slo;split => //.
case: (equal_or_not a b) => ab; [left => // | right; exists i; split].
    by rewrite sr.
   split => //; [ by rewrite - aux | dneg nab; apply: Hc =>// ].
move=> j [lji].
have : inc j (substrate r) by order_tac.
by rewrite srs; move => /set1_P => ->.
Qed.

Lemma osum_unit1 r g I:
  orsum_ax r g -> sub I (domain g) ->
  (forall i, inc i ((domain g) -s I) -> Vg g i = emptyset) ->
  (order_sum r g) \Is (order_sum (induced_order r I) (restr g I)).
Proof.
move => oa sI alz; move: (oa) => [or sr alo]. 
have dr: (domain (restr g I)) = I by aw.
have sI1: sub I (substrate r) by ue.
have oa': orsum_ax (induced_order r I) (restr g I).
  have [pa pb]:= (iorder_osr or sI1).
  hnf; rewrite pb;split => //; hnf;rewrite dr. 
  move=> i id; rewrite LgV //; apply: (alo _ (sI _ id)).
have o1: order (order_sum r g) by fprops.
have o2: order (order_sum (induced_order r I) (restr g I)) by fprops.
set E := substrate  (order_sum r g).
set F := substrate  (order_sum (induced_order r I) (restr g I)).
have EF: E = F.
  set_extens z; rewrite /E/F !orsum_sr //.
    move => zs; move: (du_index_pr1 zs) => [Qd Pd <-].
    case: (inc_or_not (Q z) I) => aux.
      by apply: disjointU_pi => //; aw;  trivial; rewrite  !LgV//; aw. 
    have Qx: inc (Q z) ((domain g) -s I) by fprops.
    have Ve := (alz _ Qx).
    by move:Pd;rewrite Ve (proj2 set0_wor) => /in_set0.
  move => zs; move: (du_index_pr1 zs) => [Qd Pd <-].
  rewrite dr in Qd; rewrite LgV //  in Pd. 
  have qq: inc (Q z) (domain g)  by  apply:sI.
  by apply: disjointU_pi; aw; trivial;rewrite LgV.    
exists (identity E).
hnf; rewrite/bijection_prop identity_s identity_t; split => //.
  split => //;apply: identity_fb.
have a1: forall x, inc x F -> inc (Q x) I.
  move=> x; rewrite /F orsum_sr // => xs; move: (du_index_pr1 xs)=> [aux _]; ue.
hnf; aw; move=> x y xE yE; rewrite idV //.
rewrite orsum_gleP orsum_gleP.
have <-: E = (sum_of_substrates g) by rewrite /E orsum_sr.
have <-: F = (sum_of_substrates (restr g I)) by rewrite /F orsum_sr.
rewrite idV ///order_sum_r -EF /glt. 
have aux: (gle (induced_order r I) (Q x) (Q y) <-> (gle r (Q x) (Q y))).
   rewrite/gle/related/induced_order; split.
     by move /setI2_P => [].
   move=> h; apply /setI2_P; split => //; apply: setXp_i; apply: a1; ue.
have ->:  Vg  (restr g I) (Q x) =  (Vg g (Q x)).
  rewrite LgV //;apply: a1; ue.
by split; move => [pa pb pc];split => //; case: pc => //; try (by right);
 move => [/aux pd pe];left.
Qed.

Lemma osum_unit2 r g I:
  worder_on r (domain g) -> ordinal_fam g ->
  sub I (domain g) ->
  (forall i, inc i ((domain g) -s I) -> Vg g i = \0o) ->
  osum r g = osum (induced_order r I) (restr g I).
Proof.
move => [wor sr] odf sj alne. 
have or:= proj1 wor. 
rewrite /osum/order_sum; apply: ordinal_o_isu1.
    apply:orsum_wor; [saw |  hnf; aw => i idg;rewrite LgcV ; fprops].
  apply: orsum_wor.
    split; first by apply: induced_wor => //; ue.
    rewrite iorder_sr //; aw; trivial; ue.
  hnf; aw =>  i idg; rewrite !LgV// //; aww.
rewrite /Lgcomp.
set g1:=  (Lg (domain g) (fun z => ordinal_o (Vg g z))).
set g2:= Lg _ _. have ->: g2 = (restr g1 I).
 by rewrite /g1 /g2; aw; apply: Lg_exten  => x xd; rewrite !LgV//; apply: sj.
have dg1: domain g1 = domain g by rewrite /g1; aw. 
apply: osum_unit1.
    split; [exact | ue | ].
    by hnf; rewrite dg1; move=> i idg; rewrite /g1 LgV//; apply: ordinal_o_or. 
  ue.
rewrite dg1; move=> i ic; rewrite /g1 LgV//.
  by rewrite (alne _ ic) ordinal_o_set0.
by move: ic => /setC_P [ok _].
Qed.

Lemma oprod_unit1 r g I:
  orprod_ax r g ->  sub I (domain g) ->
  (forall i, inc i ((domain g) -s I)  ->  singletonp (substrate (Vg g i))) ->
  (order_prod r g) \Is (order_prod (induced_order r I) (restr g I)).
Proof.
move => oa sI alse; move: (oa) => [wor sr alo]. 
have dr: (domain (restr g I)) = I by aw.
have sI1: sub I (substrate r) by ue.
have [or _] := (wor).
have oa': orprod_ax (induced_order r I) (restr g I).
  hnf; aw; rewrite iorder_sr //;split => //; first by apply: induced_wor.
  hnf;rewrite dr;move=> i id.  rewrite LgV//; apply: (alo _ (sI _ id)).
have o1: order (order_prod r g) by fprops.
have o2: order (order_prod (induced_order r I) (restr g I)) by fprops.
set E := substrate  (order_prod r g).
set F := substrate  (order_prod (induced_order r I) (restr g I)).
have Ep: E = prod_of_substrates g by rewrite /E orprod_sr. 
have Fp: F = prod_of_substrates (restr g I) by rewrite /F orprod_sr.
have fg1: fgraph (fam_of_substrates (restr g I)) 
   by rewrite /fam_of_substrates ;fprops.
have fg2: fgraph (fam_of_substrates g)  by rewrite /fam_of_substrates; fprops.
have rd:= (restr_d g I).
have ta: lf_axiom  (fun z => restr z I) E F.
   move=> z; rewrite Ep Fp; move /prod_of_substratesP => [fgz dz iVV]. 
   have sj2: sub I (domain z) by ue.
   apply /prod_of_substratesP;split;aww. 
   by move=> i ij; rewrite ! LgV//; apply: iVV; apply: sI.
have specs: forall i x y, inc i (domain g) ->  ~ inc i I ->
   inc x E -> inc y E -> Vg x i = Vg y i.
  move => i x y idg nij ; rewrite Ep.
  move /prod_of_substratesP =>  [fgu du up].
  move /prod_of_substratesP =>  [fgv dv vp].
  have xc: (inc i ((domain g) -s I)) by apply /setC_P; split => //.
  move: (up _ idg) (vp _ idg) => pa pb.
  by move: (alse _ xc) => /singletonP [_]; apply.
have ri: forall u v, inc u E -> inc v E -> restr u I = restr v I -> u = v.
  move=> u v uE vE.
  move: (uE)(vE); rewrite Ep.
  move /prod_of_substratesP =>  [fgu du up].
  move /prod_of_substratesP =>  [fgv dv vp] sar.
  apply: fgraph_exten => //; [ ue | move => x ; rewrite du => xdg].
  case: (inc_or_not x I) => xI; last by apply: specs.
  move: (f_equal (Vg ^~ x) sar); rewrite !LgV//.
exists (Lf  (fun z => restr z I) E F).
hnf; saw.
  saw;apply: lf_bijective => //.
  move=> y; rewrite Ep Fp; move /prod_of_substratesP=> [fgy dy iVV].
  set x := (Lg (domain g) 
    (fun z => Yo (inc z I) (Vg y z) (rep (substrate (Vg g z))))).
  have fgx: fgraph x by rewrite /x; fprops.
  have dx: domain x = domain g by rewrite /x; aw.
  exists x.
    apply /prod_of_substratesP;split => // i idx; rewrite /x LgV //; Ytac xj. 
      rewrite rd in iVV; move: (iVV _ xj); rewrite LgV//.
    have xc: (inc i ((domain g) -s I)) by apply /setC_P; split => //.
    by move: (alse _ xc) => /singletonP [ne1 _]; apply: rep_i. 
    apply: fgraph_exten; fprops; rewrite dy; aw; trivial. 
   by  move => i ij; rewrite /x !LgV//; fprops; Ytac0.
have sjr: sub I (substrate r) by ue.
hnf; aw; move=> x y xE yE; rewrite !LfV//.
move: (xE)(yE); rewrite Ep.
move /prod_of_substratesP =>  [fgx dx xp].
move /prod_of_substratesP =>  [fgy dy yp].
have pa : substrate (induced_order r I) = I by rewrite iorder_sr.
have sjx: sub I (domain x) by rewrite dx.
have sjy: sub I (domain y) by rewrite dy.
split.
  move /(orprod_gleP oa) => [_ _ h]; apply /(orprod_gleP oa').
  rewrite -Fp;split; [by apply: ta | by apply: ta | ].
  case: h; first by move=> -> ; left.
  move => [k [ksr klt kle]]; right; rewrite pa;exists k.
  case: (inc_or_not k I) => kj.
    hnf; rewrite !LgV//; split => // i ilt.
    move: (iorder_gle4 ilt) => [ij _]; rewrite !LgV//.
    apply: (kle _ (iorder_gle2 ilt)).
  by move: klt => [_ []]; apply: specs => //; rewrite - sr.
move /(orprod_gleP oa') => [_ _ h]; apply /(orprod_gleP oa).
rewrite -Ep; split => //; case: h; first by move => h;left; apply: ri.
rewrite pa;move=> [k [ksr klt kle]]; right; exists k.
rewrite sr; split; [by apply: sI | by  move: klt; rewrite !LgV | ].
move=> i [lik nik]; case: (inc_or_not i I) => ij.
  have lik1: glt (induced_order r I) i k by  split => //; apply/iorder_gleP.
  move: (kle _ lik1); rewrite !LgV//.
apply: specs => //; rewrite -  sr;order_tac.
Qed.

Lemma oprod_unit2 r g I:
  worder_on r (domain g) -> ordinal_fam g ->
  sub I (domain g) ->
  finite_set (substrate r) ->
  (forall i, inc i ((domain g) -s I) -> Vg g i = \1o) ->
  oprod r g = oprod (induced_order r I) (restr g I).
Proof.
move=> [wor sr] ofg jd fs alz.
have or: order r by fprops.
have jsr: sub I (substrate r) by ue.
have aa: substrate (induced_order r I) = I by rewrite iorder_sr.
apply: ordinal_o_isu1.
    apply: orprod_wor => //;hnf; aw => // i idg; rewrite !LgV//; fprops.
  apply: orprod_wor.
  + by aw; split => //; apply: induced_wor.
  + hnf; aw =>  i idg; rewrite !LgV //; aww.
  + rewrite aa;  apply: (sub_finite_set jsr fs).
set g1:=  Lgcomp _ _.
have ->: (Lgcomp (restr g I) ordinal_o) = (restr g1 I).
   rewrite /g1/Lgcomp;aw; apply: Lg_exten => x xd. 
   by rewrite !LgV // ;apply: jd.
have dg1: domain g1 = domain g by rewrite /g1; aw.
apply: oprod_unit1; rewrite /orprod_ax ? dg1 //.
  split => //;move=> i idg; rewrite /g1 !LgV//; fprops; ue.
move=> i ic; move /setC_P: (ic) => [ic1 _]. 
by rewrite /g1 LgV// (alz _ ic) (ordinal_o_sr ); exists emptyset.
Qed.

Lemma orsum_assoc_iso r g r' g':
  orsum_ax r g ->  orsum_ax r' g' ->
  r = order_sum r' g' ->
  let order_sum_assoc_aux :=
    fun l =>
    order_sum (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))) in
  let  order_sum_assoc :=
    order_sum r' (Lg (domain g') order_sum_assoc_aux)
  in order_isomorphism (Lf (fun x=> J (J (P x) (P (Q x))) (Q (Q x)))
      (sum_of_substrates g) (substrate (order_sum_assoc)))
  (order_sum r g) (order_sum_assoc).
Proof.
move=> oa oa' oa_link F G.
move: (oa) => [or sr alo].
move: (oa') => [or' sr' alo'].
have alo'' :forall l, inc l (substrate r') ->
  orsum_ax  (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))).
  move=> l ls; saw; first by apply: alo' =>//; ue.
  hnf; aw;move => i isg; rewrite LgV //;apply: alo; rewrite - sr oa_link.
  rewrite orsum_sr //; apply: disjoint_union_pi1 =>// ; ue. 
have aux2 :forall l, inc l (domain g') -> order  (F l).
  move=> l ldg';  rewrite /F; rewrite - sr' in ldg'; fprops.
have oa'' : orsum_ax r' (Lg (domain g') F).
  hnf; saw; hnf; aw.
  by move => i idf; rewrite LgV//; apply: aux2.
have org : order G by rewrite /G; fprops.
have ta:  (lf_axiom (fun x => J (J (P x) (P (Q x))) (Q (Q x))) 
        (sum_of_substrates g) (substrate G)). 
  move=> x xs; rewrite /G; aw; move: (du_index_pr1 xs) => [Qd Ps px].
  move: Qd;rewrite - sr oa_link. rewrite !orsum_sr // => Qd.
  move: (du_index_pr1 Qd) => [QQd PQs pQ].
  apply: disjoint_union_pi1; aw; trivial; rewrite LgV// /F orsum_sr //.
    by apply: disjoint_union_pi1;aw; trivial; rewrite LgV // pQ.
  apply: alo''; ue.
set(FF:= Lf  (fun x  => J (J (P x) (P (Q x))) (Q (Q x)))
    (sum_of_substrates g) (substrate G)).
have injF: injection FF. 
  apply: lf_injective => //. 
  move => u v us vs eq.
  move: (du_index_pr1 us) (du_index_pr1 vs) => [Qu _ <-][Qv _ <-].
  move: (pr1_def eq) (pr2_def eq)=> eq1 eq2.
  move: Qu Qv;rewrite - sr oa_link; rewrite orsum_sr // => Qu Qv.
  move: (du_index_pr1 Qu)(du_index_pr1 Qv) =>  [_ _ <-][_ _ <-].
  by rewrite eq2 (pr1_def eq1) (pr2_def eq1).
have bF: (bijection FF).
  split =>//; apply: lf_surjective => //. 
  move=> y; rewrite /G orsum_sr // => yG.
  move: (du_index_pr1  yG); rewrite Lgd=> [[Qd]]; rewrite LgV//; move=> Py Qpy.
  rewrite sr' in alo''; move: (alo'' _ Qd) => al.
  move: (Py); rewrite /F orsum_sr // => paux.
  move: (du_index_pr1 paux);rewrite Lgd => [[PQd]]; rewrite LgV //; move=> PPy Ppy.
  set (x:= J (P (P y)) (J (Q (P y)) (Q y))).
  have xs: (inc x (sum_of_substrates g)).
    rewrite /x;apply: disjoint_union_pi1 =>//.
    by rewrite - sr oa_link orsum_sr //; apply: disjoint_union_pi1.
  by ex_tac; rewrite /x ; aw; rewrite Ppy Qpy.
rewrite /FF;hnf; split; fprops; first by saw; rewrite orsum_sr.
hnf; aw;move=> x y xs ys; rewrite !LfV//.
set gx := (J (J (P x) (P (Q x))) (Q (Q x))).
set gy := (J (J (P y) (P (Q y))) (Q (Q y))).
move: (du_index_pr1 xs)(du_index_pr1 ys) => [Qu Pu pu][Qv Pv pv].
move: Qu Qv;rewrite - sr oa_link (orsum_sr oa') => Qu Qv.
move: (du_index_pr1 Qu)(du_index_pr1 Qv) =>  [QQx PQx pqu][QQy pQy pqv].
set P1:=inc gx (sum_of_substrates (Lg (domain g') F)).
set P2:=inc gy (sum_of_substrates (Lg (domain g') F)).
have p1p: P1.
  rewrite /P1; apply: disjoint_union_pi1; aw; trivial;rewrite LgV//.
  have Qs: inc (Q (Q x)) (substrate r') by ue.
  rewrite /F orsum_sr //; try apply: alo'' =>//.
  by  apply: disjoint_union_pi1; [ rewrite Lgd // | aw; rewrite LgV // pqu].
have p2p: P2.
  rewrite /P2; apply: disjoint_union_pi1; aw; trivial.
  have Qs: inc (Q (Q y)) (substrate r') by ue.
  rewrite LgV// /F orsum_sr //; try apply: alo'' =>//.  
  by apply: disjoint_union_pi1; [ rewrite Lgd // | rewrite LgV //pqv].
split; move /orsum_gleP => [_ _ h]; apply /orsum_gleP; split => //.
  have aux1: inc (Q (Q x)) (substrate r') by ue.
  hnf; rewrite /gx !pr1_pair !pr2_pair LgV//.
  move: (alo'' _ aux1) => aux2'.
  case: h.
    move => [] /orsum_gleP [Qx1 Qx2 hr] nxy.
    case: hr; first by left.
    move => [aa bb]; right; split => //; apply /orsum_gleP;split => //.
        by apply: disjoint_union_pi1; aw; trivial;rewrite LgV//  pqu.
      by rewrite aa;apply: disjoint_union_pi1; aw; trivial;rewrite ! LgV// pqv.
   hnf; rewrite !pr2_pair (LgV PQx) !pr1_pair pqu.
   case: (equal_or_not (P (Q x)) (P (Q y)))=> aux5; last by left;split.
   by case: nxy; rewrite -pqu - pqv aa aux5.
  move=> [sq le1]; right;rewrite - sq; split => //.
  apply /orsum_gleP;split => //.
      by apply:disjoint_union_pi1; aw; trivial;rewrite LgV //pqu.
    by rewrite sq;apply: disjoint_union_pi1; aw; trivial;rewrite LgV// pqv.
  by right;hnf; aw; rewrite LgV// pqu.
move:h;rewrite/order_sum_r /gx /gy !pr1_pair !pr2_pair; case.
  move=> [le ne] ; left; split; last by dneg ne1; ue.
  by apply /orsum_gleP;split => //; left.
move=> [qq]; rewrite LgV //.
have Qs: inc (Q (Q x)) (substrate r') by ue.
move /orsum_gleP => [_ _]. rewrite/order_sum_r LgV//; aw; trivial.
case; move =>  [hyp1 hyp2].
  have aux2': Q x <> Q y by dneg ne1; ue.
  left; split => //;  apply /orsum_gleP;split => //; right;split => //.
right; split => //; first by apply: pair_exten.
by move: hyp2; rewrite pqu.
Qed.

Lemma orprod_assoc_iso r g r' g':
  orprod_ax r g ->  orsum_ax r' g' ->
  r = order_sum r' g' ->
  worder r' ->
  (forall i, inc i (domain g') -> worder(Vg g' i)) ->
  let order_sum_assoc_aux :=
    fun l =>
    order_prod (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))) in
  let  ordinal_prod_assoc :=
    order_prod r' (Lg (domain g') order_sum_assoc_aux)
  in order_isomorphism (Lf
     (fun z  => Lg (domain g') (fun l  => 
       Lg (substrate (Vg g' l)) (fun j => Vg z (J j l))))
      (prod_of_substrates g) (substrate (ordinal_prod_assoc)))
  (order_prod r g) (ordinal_prod_assoc).
Proof.
move=> la oa  oa_link wor' alwo F G.
move: (oa) => [or' sr' alo']. 
move: (la) => [wor sr alo]. 
have dgpr: forall i j, inc i (domain g') -> inc j (substrate (Vg g' i)) ->
   inc (J j i) (domain g).
  move=> i j id jd; rewrite - sr oa_link; rewrite orsum_sr //. 
  by apply: disjoint_union_pi1 =>//.
have la1: forall i, inc i (domain g') ->
   orprod_ax (Vg g' i)
     (Lg (substrate (Vg g' i)) (fun i0 : Set => Vg g (J i0 i))).
   move=> i idg; split;aww.
   hnf; aw; move=> j js; rewrite LgV// ; apply: alo; apply: dgpr =>//.
have la': orprod_ax  r' (Lg (domain g') F).
  split => //;hnf;aw;trivial;move=> i idg'; rewrite /F LgV//; fprops.  
have oG: order G by rewrite /G; fprops.
have s1: substrate (order_prod r g) = prod_of_substrates g by rewrite orprod_sr.
have sG1: substrate G = productb (Lg (domain g') (fun i => substrate (F i))).
  rewrite /G orprod_sr // /prod_of_substrates /fam_of_substrates Lgd.
  by apply: f_equal; apply: Lg_exten; move=> i idg /=; rewrite LgV.
have sG0: substrate G = (prod_of_substrates (Lg (domain g') F)).
  rewrite /G orprod_sr // /prod_of_substrates /fam_of_substrates Lgd.
have sG2: substrate G = productb
      (Lg (domain g') (fun i => productb
        (Lg (substrate (Vg g' i))(fun i0 => substrate (Vg g (J i0 i)))))).
  rewrite sG1; f_equal; apply: Lg_exten.
  move=> i idg; rewrite /F orprod_sr //; last by apply: la1.
  congr productb; rewrite /fam_of_substrates; aw.
  by apply: Lg_exten; move=> x xs /=; rewrite LgV//.
pose h z := Lg (domain g') (fun l  => 
     Lg (substrate (Vg g' l)) (fun j => Vg z (J j l))).
have p1: forall z, inc z (prod_of_substrates g) -> inc (h z) (substrate G).
  move=> z zp; move: (zp) => /prod_of_substratesP  [fgz dz iVV].
  rewrite sG2; apply /setXf_P; rewrite /h;split;[fprops | by aw | ]. 
  move=> i idg; rewrite LgV//; apply /setXf_P;split;aww.
  move => j js; rewrite LgV//; apply: iVV; exact (dgpr _ _ idg js). 
have p2: forall a b, inc a (prod_of_substrates g) ->
   inc b  (prod_of_substrates g) ->  h a = h b -> a = b.
  move=> a b  /prod_of_substratesP  [fga da iVVa]
   /prod_of_substratesP [fgb db iVVb] eqn.
  apply: fgraph_exten =>//; try ue; move=> x xda.
  move: xda; rewrite da - sr oa_link; rewrite orsum_sr // => xsr.
  move: (du_index_pr1 xsr) => [Qx Px px].
  move: (f_equal (Vg ^~ (Q x)) eqn) => eq2.
  by move: (f_equal (Vg ^~ (P x)) eq2); rewrite /h !LgV//; rewrite px.
have p3: forall x, inc x (substrate G) -> exists2 z,
  inc z (prod_of_substrates g) &  x = (h z).
  move=> x;rewrite sG2 => /setXf_P [fgx dx iVVx].
  exists (Lg (domain g) (fun w => Vg (Vg x (Q w)) (P w))).
  apply /prod_of_substratesP; split;aww; move=> i idg; rewrite LgV//.
    move : idg; rewrite - sr oa_link; rewrite orsum_sr // => xsr.
    move: (du_index_pr1 xsr) => [Qx Px px]; move: (iVVx _ Qx). 
    move /setXf_P => [fg1 d1 ivv1].
    by rewrite -{3} px; apply: ivv1.
  rewrite /h; symmetry;apply: fgraph_exten =>//;[ fprops | aw; ue | aw].
  move=> j jdg /=; rewrite LgV//; move: (iVVx _ jdg) => /setXf_P  [fgj dj iVV2].
  apply: fgraph_exten; [ fprops | exact | aw; ue| aw].
  by move=> w ws; rewrite !LgV//; aw; trivial; apply: dgpr.
split;fprops; aw; first by saw => //;apply: lf_bijective.
hnf; rewrite lf_source ; move=> a b ap bp; rewrite !LfV //.
split.
  move /(orprod_gleP la) => [_ _ ha]; apply/(orprod_gleP la').
  split; first by rewrite - sG0; apply: p1.
     by rewrite - sG0; apply: p1.
  case: ha; first by move=> ->; left.
  move=> [j [jsr [jlt diff] jle]]; right.
  move: jsr; rewrite oa_link; rewrite orsum_sr // => jsg'.
  move: (du_index_pr1 jsg') => [Qx Px px].
  rewrite  sr';ex_tac.
    have paux: forall c, inc c (prod_of_substrates g) ->
      inc (Vg  (h c) (Q j)) (prod_of_substrates
        (Lg (substrate (Vg g' (Q j))) (fun i : Set => Vg g (J i (Q j))))).
      move=> i ic;move: (p1 _ ic); rewrite sG1.
      move /setXf_P=> [fgh dh ivv];  move: (ivv _ Qx); aw.
      rewrite /F orprod_sr //; apply: la1 => //.
    rewrite -/(h a) - /(h b) LgV//; rewrite /F ;split; last first.
       rewrite /h LgV//; dneg aa; move: (f_equal (Vg ^~(P j)) aa).
       by rewrite !LgV// px.
    apply/(orprod_gleP (la1 _ Qx));split => //; try apply: paux => //.
    right; ex_tac; rewrite LgV//.
      by rewrite /h !LgV // px. 
    move=> i [ile ne].
    have isr: inc i (substrate (Vg g' (Q j))) by order_tac.
    rewrite /h !LgV//; apply: jle; split; last by dneg  aa; rewrite -aa; aw.
    rewrite oa_link; apply /orsum_gleP; split => //.
    apply: disjoint_union_pi1=> //.
    by right; aw.
  move=> i ilt. 
  have idg: inc i (domain g') by rewrite - sr'; order_tac.
  rewrite /h !LgV//; apply: Lg_exten =>// k ks.
  apply: jle; split; last by move: ilt => [_ bad]; dneg aa; rewrite -aa; aw.
  rewrite oa_link; apply /orsum_gleP;split => //.
  - by apply: disjoint_union_pi1.
  - by hnf; aw; left.
move/(orprod_gleP la') => [_ _ ha]; apply /(orprod_gleP la);split => //.
case: ha; first by move=> eq; left; apply: p2.
move=> [j [jsr jlt jle]]; right.
rewrite sr' in jsr; move: jlt; rewrite /h /F !LgV//; move=> [le ns].
move: le; move /(orprod_gleP (la1 _ jsr)).
move=> [p6 p7];case; first by move=> p8; case: ns.
move=> [k [ks klt kle]].
rewrite sr; move: (dgpr _ _ jsr ks) => pd.
ex_tac; first by  move: klt; rewrite !LgV//.
move=> i [lei nei]; move: lei;rewrite oa_link=> lti.
have : inc i (substrate (order_sum r' g')) by order_tac.
rewrite orsum_sr // => iso; move: (du_index_pr1 iso) => [Qdg Psg' pi].
move: (orsum_gle1 lti); aw; case => ch.
  move: (jle _ ch); rewrite /h !LgV// => eq1.
  by move: (f_equal (Vg ^~(P i)) eq1); rewrite !LgV//; rewrite pi.
move: ch => [Qi aux].
have ->: i = J (P i) j by rewrite -Qi; aw.
have aux2: glt (Vg g' j) (P i) k.
  by  rewrite -Qi; split => //; dneg aa; rewrite -aa - Qi pi; aw.
rewrite Qi in Psg'; move: (kle _ aux2); rewrite !LgV//.
Qed.

Lemma osum_assoc1 r g r' g':
  worder_on r (domain g)  ->
  worder_on r' (domain g') -> 
  ordinal_fam g -> worder_fam g' ->
  r = order_sum r' g' ->
  let order_sum_assoc_aux :=
    fun l =>
    osum (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))) in
  osum r g = osum r' (Lg (domain g') (order_sum_assoc_aux)).
Proof.
move=> [wor sr] [wor' sr'] alB  alw oal osa.
have oa': orsum_ax r' g'.
   split;fprops; move => j jd; exact (proj1 (alw _ jd)).
apply: ordinal_o_isu1.
    apply: orsum_wor; [saw| hnf; aw => i idg /=; rewrite LgcV; fprops].
  apply: orsum_wor; [saw|hnf; aw=> i idg;rewrite !LgV//; aw; trivial ].
  apply: ordinal_o_wor; rewrite /osa;apply: OS_sum=> //.
    by aw; split => //; apply:alw.
  hnf; aw  => j js; rewrite LgV//;apply: alB;rewrite - sr oal (orsum_sr oa').
  by apply: disjoint_union_pi1.
set g'' := (Lgcomp g ordinal_o).
have oa: orsum_ax r g''. 
  rewrite /g'';hnf; saw;fprops; hnf; aw; move=> i idg.
  rewrite LgcV //; fprops.
move: (orsum_assoc_iso oa oa' oal) => /=.
pose aux' l:= order_sum (Vg g' l)
   (Lg (substrate (Vg g' l))(fun i=> Vg g'' (J i l))).
set f:= Lf _ _ _. 
move => oi1; move: (oi1) => [o1 o2 _ _].
apply: (@orderIT (order_sum r' (Lg (domain g') aux'))); first by exists f. 
apply: orsum_invariant2 =>//;aww.
rewrite sr' /Lgcomp;move=> i isr; rewrite !LgV// /osa /osum; aw; trivial.
set s:= order_sum _ _.
have -> : aux' i = s.
  rewrite /aux' /s/Lgcomp; aw; f_equal; apply: Lg_exten;move=> j js.
  have pd: inc (J j i) (domain g). 
    rewrite - sr oal (orsum_sr oa'); by apply: disjoint_union_pi1.
  by rewrite /g'' LgcV// LgV//.
apply: ordinal_o_is; apply: orsum_wor; first by split; [ apply: alw | aw].
hnf; aw;move=> j js; rewrite LgcV// ? Lgd // LgV//.
apply: ordinal_o_wor; apply: alB.
rewrite - sr  oal (orsum_sr oa');  by apply: disjoint_union_pi1.
Qed.

Lemma oprod_assoc1 r g r' g':
  worder_on r (domain g) ->
  worder_on r' (domain g') -> 
  ordinal_fam g -> worder_fam g' ->
  r = order_sum r' g' ->
  finite_set (substrate r) ->finite_set (substrate r') ->
  (forall i, inc i (domain g') ->  finite_set (substrate (Vg g' i))) ->
  let order_prod_assoc_aux :=
    fun l =>
    oprod (Vg g' l) (Lg (substrate (Vg g' l)) (fun i => Vg g (J i l))) in
  oprod r g = oprod  r' (Lg (domain g') order_prod_assoc_aux).
Proof.
move=> [wor sr] [wor' sr'] alB alw oal fs fs' alfs osa.
have oa': orsum_ax r' g'.
  split;fprops; hnf; move => j jd; exact (proj1 (alw _ jd)).
apply: ordinal_o_isu1.
    apply: orprod_wor; hnf; aw => //; move=> i idg; rewrite !LgV //; fprops.
  apply: orprod_wor; hnf; aw => // i idg'; rewrite !LgV//; aw; trivial.
  apply: ordinal_o_wor.
  rewrite /osa; apply:OS_prod; first by split; aww.
    hnf; aw;move => j js; rewrite LgV//; apply: alB.
    rewrite - sr  oal (orsum_sr oa').
    by apply: disjoint_union_pi1.
  by apply: alfs.
set g'' := Lgcomp _ _.
have oa: orprod_ax r g''.
  rewrite /g'';hnf; saw  => //;hnf; aw; move=> i idg; rewrite !LgV//; fprops.
move: (orprod_assoc_iso oa oa' oal wor' alw) => /=.
pose ax' l := order_prod (Vg g' l)
  (Lg (substrate (Vg g' l))(fun i=> Vg g'' (J i l))).
set f:= Lf _ _ _.
move => oi1; move: (oi1) => [o1 o2 _ _].
apply: (@orderIT  (order_prod r' (Lg (domain g') ax'))); first by exists f. 
apply: orprod_invariant2 =>//; aww.
rewrite sr';move=> i isr;aw; rewrite /osa /oprod !LgV//; aw; trivial.
set s:= order_prod _ _.
have -> : (ax' i = s).
  rewrite /ax' /s /Lgcomp; aw; f_equal; apply: Lg_exten;move=> j js.
  have pd: inc (J j i) (domain g). 
    by rewrite - sr oal (orsum_sr oa');  by apply: disjoint_union_pi1.
  rewrite /g'' ! LgV//.
apply: ordinal_o_is;apply: orprod_wor; [ by split; aww | | fprops].
hnf; aw;move=> j js; rewrite !LgV //;aw;trivial;  apply: ordinal_o_wor; apply: alB.
rewrite - sr  oal (orsum_sr oa');  by apply: disjoint_union_pi1.
Qed.

Lemma osum_rec_def a b: ordinalp a -> ordinalp b ->
  a +o b = a \cup fun_image b (osum2 a).
Proof.
move => oa; move: b; apply: least_ordinal2' => c oc prc.
set r := (order_sum2 (ordinal_o a) (ordinal_o c)).
have woc:worder r by apply: orsum2_wor; apply: ordinal_o_wor.
move: (sub_osr a) (sub_osr c) => [ora sra][orc src].
move: C1_ne_C0 C0_ne_C1 => ha hb.
pose f x := Yo (Q x = C0) (P x) (a +o (P x)).
have sr: substrate r = canonical_du2 a c by rewrite /r orsum2_sr // sra src.
suff h: forall x, inc x (substrate r) -> f x = fun_image (segment r x) f.
  move:(ordinal_isomorphism_exists woc); rewrite -/(ordinal _) -/(a +o c).
  move => [o1 o2 [[[fuf _] bf] sf tf] sif]. rewrite ordinal_o_sr in tf.
  rewrite -tf; set_extens w=> [/(proj2 bf) | /setU2_P[wt1 | /funI_P [z zc ->]]].
  - rewrite sf; move => [p ps ->]; apply /setU2_P.
    rewrite -(transdef_tg3 woc  h ps).
    move: ps; rewrite sr => /candu2P [pp hh].
    rewrite /f; case: hh => [] [p1 ->]; Ytac0;first by left.
    right;apply/funI_P; ex_tac.
  - have xsr: inc (J w C0) (substrate r) by rewrite sr; apply: candu2_pra.
    move: (transdef_tg3 woc  h xsr).
    rewrite /f; aw; Ytac0 => ->; Wtac.
  - have xsr: inc (J z C1) (substrate r) by rewrite sr; apply: candu2_prb.
    move: (transdef_tg3 woc h xsr).
    rewrite /f; aw; Ytac0 => ->;Wtac.
move => x; rewrite sr =>/candu2P [px]; case=> [][Px Qx]; rewrite /f.
  Ytac0; set_extens t.
    move => tp; apply /funI_P; exists (J t C0); last by aw; Ytac0.
    move: (ordinal_transitive oa Px tp)(Os_ordinal oa Px) => ta opx.
    apply /segmentP; split.
       apply /orsum2_gleP; rewrite sra src; split => //.
       + by apply: candu2_pra.
       + by rewrite - px Qx; apply: candu2_pra.
       + constructor 1; saw  => //; apply /ordo_leP; split => //.
         apply: (ordinal_transitive opx tp).
    by move => h;case: (ordinal_irreflexive opx); rewrite -{1} h; aw.
  move => /funI_P [z /segmentP [/orsum2_gleP s1 nzx] ->].
  move: s1;  rewrite sra src; aw;move => [/candu2P [pz _]  _]; case.
  + move => [q1 _ /ordo_leP [q5 q6 q7]]; Ytac0.
    case: (ordinal_sub (Os_ordinal oa q5) (Os_ordinal oa q6) q7) => //.
    move => sp; case: nzx; apply: pair_exten => //;ue.
  + by move => [_]; case.
  + by move => [_]; case.
rewrite Qx; Ytac0; rewrite (prc _ Px);set_extens t.
  case /setU2_P.
    move => ta; apply /funI_P; exists (J t C0); last by aw; Ytac0.
    apply /segmentP; split; last by move => e; case: ha; rewrite - Qx -e; aw.
    apply /orsum2_gleP; rewrite sra src; split => //.
    + by apply: candu2_pra.
    + by apply /candu2P; split => //;right.
    + by constructor 3; rewrite Qx;aw.
  move => /funI_P [z zp ->];apply /funI_P; exists (J z C1); last by aw; Ytac0.
  move: (ordinal_transitive oc Px zp)(Os_ordinal oc Px) => ta opx.
  apply /segmentP; split; last first. 
    by move => h;case: (ordinal_irreflexive opx); rewrite -{1} h; aw.
  apply /orsum2_gleP; rewrite sra src; split => //.
  + by apply: candu2_prb.
  + by apply /candu2P; split => //;right.
  + constructor 2; rewrite Qx;aw; split => //; apply /ordo_leP; split => //.
    exact: (ordinal_transitive  opx zp).
move /funI_P => [z /segmentP  [/orsum2_gleP s1 s2] ->].
move: s1;  rewrite sra src; aw;move => [/candu2P [pz p4] _ p5]; case: p4.
  by move => [Pz Qz]; Ytac0; apply /setU2_P; left.
move => [Pz Qz]; rewrite Qz; Ytac0; case: p5; rewrite Qz; move => [] //.
move => _ _ /ordo_leP [_ _ h3]; apply /setU2_P; right; apply /funI_P.
exists (P z) => //.
case: (ordinal_sub (Os_ordinal oc Pz) (Os_ordinal oc Px) h3) => //.
move => e; case: s2; apply: pair_exten => //;ue.
Qed.


Lemma oprod_rec_def a b: ordinalp a -> ordinalp b ->
  a *o b = fun_image (a\times b) (fun z => a *o (Q z) +o (P z)).
Proof.
move => oa; move: b; apply: least_ordinal2' => c oc prc.
set r := (order_prod2 (ordinal_o a) (ordinal_o c)).
have woc:worder r by apply: orprod2_wor; apply: ordinal_o_wor.
move: (sub_osr a) (sub_osr c) => [ora sra][orc src].
pose f x := a *o (Vg x C0) +o  (Vg x C1).
have sr: substrate r = product2 c a by rewrite /r orprod2_sr // sra src.
suff h: forall x, inc x (substrate r) -> f x = fun_image (segment r x) f.
  move:(ordinal_isomorphism_exists woc); rewrite -/(ordinal _) -/(a *o c).
  move => [o1 o2 [[[fuf _] bf] sf tf] sif]; rewrite ordinal_o_sr in tf.
  rewrite - tf; set_extens w => wt.
    move /(proj2 bf):wt; rewrite sf; move => [p ps ->]; apply /funI_P.
    move:(transdef_tg3 woc  h ps) => <-.
    move: ps; rewrite sr => /setX2_P [fp dp vpa vpb].
    by exists (J (Vg p C1) (Vg p C0)); [ fprops | aw].
  move /funI_P: wt => [z /setX_P [pz pza qzb] ->].
  set x := variantLc (Q z) (P z).
  have xsr: inc x (substrate r).  
     rewrite sr; rewrite /x;apply /setX2_P; split => //;aww.
  move: (transdef_tg3 woc h xsr).
  rewrite /f {1 2}/x; aw => ->;Wtac.
move => x; rewrite sr => /setX2_P [fp dp vpa vpb]; rewrite /f. 
set u :=  (Vg x C0); set v :=  (Vg x C1).
have ou:=(Os_ordinal oc vpa).
have ov:=(Os_ordinal oa vpb).
rewrite (osum_rec_def (OS_prod2 oa ou) ov).
set_extens t.
  have xca:inc x (product2 c a) by apply/setX2_P.
  case/setU2_P.
    rewrite (prc _ vpa); move =>/funI_P [z /setX_P[p za zb] ->].
    apply /funI_P; exists (variantLc (Q z) (P z)); aw; trivial.
    move: (Os_ordinal ou zb)=> oqz.
    have sa: Q z <> Vg x C0.
      by move => s;apply: (ordinal_irreflexive oqz); rewrite {2} s.
    have qzc:=(ordinal_transitive oc vpa zb).
    apply/segmentP; split; last first. 
      by move => sv; move: (f_equal (Vg ^~C0) sv); aw.
    apply/(orprod2_gleP ora orc); rewrite sra src; split => //.
    + apply/setX2_P; split => //; aww.
    + right; aw; split => //; apply /ordo_leP; split => //. 
      apply: (ordinal_transitive ou zb).
  move => /funI_P [z za ->];apply /funI_P; exists (variantLc u z); aw; trivial.
  have iza:=(ordinal_transitive oa vpb za).
  apply/segmentP; split; last first. 
      move => sv; move: (f_equal (Vg ^~C1) sv); aw.
      by move => s;apply: (ordinal_irreflexive ov); rewrite -{1} s.
    apply/(orprod2_gleP ora orc); rewrite sra src; split => //.
    + apply/setX2_P; split => //; aww.
    + left;aw; split => //; apply /ordo_leP; split => //.
      apply: (ordinal_transitive ov za).
move => /funI_P [z /segmentP[/(orprod2_gleP ora orc) za zb] ->] .
move: za; rewrite sra src; move => [/setX2_P [z1 z2 z3 z4] _]; case.
  move => [sv /ordo_leP [z5 z6 z7]]; apply /setU2_P; right.
  apply/funI_P; rewrite sv; exists (Vg z C1) => //.
  case: (ordinal_sub (Os_ordinal oa z4) ov z7) => //h ; case: zb.
  by apply: fgraph_exten => //; [ue | rewrite z2 => uu; move /C2_P; case => ->].
move => [/ordo_leP [z5 z6 z7] sv]; apply /setU2_P; left.
rewrite (prc _ vpa); apply /funI_P; exists (J (Vg z C1) (Vg z C0)); aw; trivial.
move: (Os_ordinal oc z3)(Os_ordinal oc z5)  => o1 o2.
by apply :setXp_i => //; apply /oltP. 
Qed.

Lemma oprod_zero r g: 
  (exists2 i, inc i (domain g) & substrate (Vg g i) = emptyset) ->
  order_prod r g = emptyset.
Proof.
move=> [j jdg Vz].
apply /set0_P => q /Zo_P [] /setX_P [_ /setXf_P [fgy dy p]].
by move: (p _ jdg); rewrite Vz => /in_set0.
Qed.

Lemma oprod0r x:  x *o \0o = \0o.
Proof.
rewrite /oprod2 /order_prod2 oprod_zero ?ordinal0_pr //.
aw; exists C0 => //; aww.
rewrite ordinal_o_set0;exact: (proj2(set0_wor)).
Qed.
  
Lemma oprod0l x: \0o *o x = \0o.
Proof. 
rewrite /oprod2 /order_prod2 oprod_zero ?ordinal0_pr //.
aw; exists C1 => //; aww.
rewrite ordinal_o_set0;exact: (proj2(set0_wor)).
Qed.

Lemma osum0r a: ordinalp a -> a +o \0o = a.
Proof. by move => ox; rewrite (osum_rec_def ox OS0) funI_set0 setU2_0. Qed.

Lemma osum0l a: ordinalp a -> \0o +o a = a.
Proof.
move: a; apply: least_ordinal2' => c oc prc.
rewrite (osum_rec_def OS0 oc) set0_U2; set_extens t.
  by move => /funI_P [z zc ->]; rewrite prc.
by move => tc; apply/funI_P; ex_tac; rewrite prc.
Qed.

Lemma oprod1r a: ordinalp a -> a *o \1o  = a.
Proof. 
move=> ox; rewrite (oprod_rec_def ox OS1). 
have h: forall t, inc t a -> t = a *o \0o +o t.
   move => t tx; rewrite oprod0r osum0l //; exact: (Os_ordinal ox tx).
set_extens t.
  by move/funI_P => [z /setX_P [p1 p2 /set1_P ->] ->]; rewrite - h.
move => tx; apply /funI_P; exists (J t \0o); last by aw; apply h.
by apply:setXp_i; fprops; apply/set1_P.
Qed.

Lemma oprod1l a: ordinalp a -> \1o *o a  = a.
Proof. 
move: a; apply:least_ordinal2' => c oc H.
rewrite (oprod_rec_def OS1 oc); set_extens t.
  move/funI_P => [z /setX_P [p1 /set1_P -> p2] ->]. 
  rewrite H // osum0r //; exact: (Os_ordinal oc p2).
move => tc; apply /funI_P; exists (J \0o t).
  by apply:setXp_i; fprops; apply/set1_P.
aw; rewrite H // osum0r //; exact:(Os_ordinal oc tc).
Qed.

Lemma osucc_pr a: ordinalp a -> a +o \1o = osucc a. 
Proof. by move => ox; rewrite (osum_rec_def ox OS1) funI_set1 osum0r. Qed.

Lemma osumA a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  a +o (b +o c) = (a +o b) +o c.
Proof. 
move => oa ob; move:c; apply:least_ordinal2' => d od H.
rewrite (osum_rec_def oa (OS_sum2 ob od)) (osum_rec_def ob od).
rewrite (osum_rec_def (OS_sum2 oa ob) od) {1} (osum_rec_def oa ob).
set_extens t; case /setU2_P => h; apply /setU2_P.
- left; fprops.
- move /funI_P:h  => [z /setU2_P ha ->]; case: ha.
    move => zb; left; apply /setU2_P;right; apply/funI_P;ex_tac.
  move => /funI_P [w wd ->]; rewrite (H _ wd); right; apply/funI_P; ex_tac. 
- case /setU2_P :h; first by left.
   move /funI_P => [z za ->]; right; apply /funI_P; exists z; fprops.
- right; apply /funI_P; move/funI_P: h => [z zd ->]; rewrite - (H _ zd).
  exists (b +o z) => //;apply /setU2_P; right; apply /funI_P; ex_tac.
Qed.

Lemma oprodD a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  c *o (a +o b) = (c *o a) +o (c *o b).
Proof.
move => oa ob oc; move: b ob; apply:least_ordinal2' => d od H.
move: (OS_prod2 oc oa) (OS_prod2 oc od) => oca ocd.
rewrite (oprod_rec_def oc (OS_sum2 oa od)) (osum_rec_def oa od).
rewrite (osum_rec_def oca ocd) {1}(oprod_rec_def oc oa)(oprod_rec_def oc od).
set_extens t.
  move/funI_P => [z /setX_P[pz Pz /setU2_P Qz] ->];case: Qz => h; apply/setU2_P.
    left; apply /funI_P; exists (J (P z) (Q z)); aww.
  right; move/funI_P:h => [u ud ->]; rewrite (H _ ud).
  rewrite - (osumA oca (OS_prod2 oc (Os_ordinal od ud)) (Os_ordinal oc Pz)).
  apply/funI_P; exists (c *o u +o P z) => //; apply/funI_P.
  exists (J (P z) u); aww.
case /setU2_P; move/funI_P=> [z za ->]; apply/funI_P.
  move/setX_P: za => [pr pa pb]; exists z => //;apply /setX_P; split;fprops.
move/funI_P: za => [w /setX_P [pr pa pb] ->].
rewrite (osumA oca (OS_prod2 oc (Os_ordinal od pb)) (Os_ordinal oc pa)).
rewrite - (H _ pb); exists (J (P w) ( a +o Q w)); aw; trivial.
apply:setXp_i => //.
apply /setU2_P; right; apply /funI_P; ex_tac.
Qed.

Lemma oprodA a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  a *o (b *o c) = (a *o b) *o c.
Proof. 
move => oa ob; move: c; apply: least_ordinal2' => d od H.
rewrite (oprod_rec_def oa (OS_prod2 ob od)) (oprod_rec_def ob od).
rewrite (oprod_rec_def (OS_prod2 oa ob) od) {1} (oprod_rec_def oa ob).
set_extens t; case /funI_P => [z za ->]; apply /funI_P.
  move /setX_P:za=> [pz p1z /funI_P [u /setX_P [ppz p2z p3z] ->]].
  move:(Os_ordinal ob p2z)(Os_ordinal od p3z)(Os_ordinal oa p1z)=> opu oqu opz.
  have obqu:= (OS_prod2 ob oqu). 
  rewrite (oprodD obqu opu oa).
  rewrite - (osumA (OS_prod2 oa obqu) (OS_prod2 oa opu)opz) (H _ p3z).
  exists (J (a *o P u +o P z) (Q u)); aw;trivial;apply: setXp_i => //.
  by apply/funI_P; exists (J (P z) (P u)); aw;trivial;apply: setXp_i.
move /setX_P:za=> [pz  /funI_P [u /setX_P [pu p1 p2] ->] qzd].
move:(Os_ordinal oa p1)(Os_ordinal ob p2)(Os_ordinal od qzd)=> opu oqu oqz.
rewrite (osumA (OS_prod2 (OS_prod2 oa ob) oqz) (OS_prod2 oa oqu) opu).
rewrite -(H _ qzd) - (oprodD (OS_prod2 ob oqz) oqu oa).
exists (J (P u) (b *o Q z +o Q u)); aw; trivial;apply: setXp_i => //.
by apply /funI_P;exists (J (Q u) (Q z)); aw; trivial;apply: setXp_i.
Qed.


(** Utilitaries for the Cantor Normal Form *)

Definition osumf (f: fterm) :=
  induction_term (fun n v => f n +o v) \0o.

Definition oprodf (f: fterm) :=
  induction_term (fun n v => v *o f n) \1o.

Lemma osum_f0 f: osumf f \0c = \0o.
Proof. exact: induction_term0. Qed.

Lemma oprod_f0 f: oprodf f \0c = \1o.
Proof. exact: induction_term0. Qed.

Lemma osum_fS n f: natp n ->  
  osumf f (csucc n) = f n +o (osumf f n).
Proof. move => nb; exact: induction_terms. Qed.

Lemma oprod_fS n f: natp n -> 
  oprodf f (csucc n) = (oprodf f n) *o (f n).
Proof. move => nb; exact: induction_terms. Qed.

Lemma osum_f1 f: ordinalp (f \0c) -> osumf f \1c = f \0c.
Proof. 
by move => h; rewrite - succ_zero (osum_fS _ NS0) osum_f0 osum0r.
Qed.

Lemma oprod_f1 f: ordinalp (f \0c) -> oprodf f \1c = f \0c.
Proof. 
by move => h; rewrite - succ_zero (oprod_fS _ NS0) oprod_f0 oprod1l.
Qed.

Definition ord_below (f:fterm) n := (forall k, k<c n -> ordinalp (f k)).
Definition same_below (e e': fterm) n:= (forall i, i <c n -> e i = e' i).

Lemma true_below_rec (P:property) n: natp n ->
  (forall i, i <c (csucc n) -> P i) -> (forall i, i<c n -> P i) /\ P n.
Proof.
move => nN H; split.
  move => k kn; apply: H; exact:(clt_leT kn (cleS nN)).
by apply: H; apply: cltS.
Qed. 

Lemma OS_osumf n f: natp n ->  ord_below f n ->
  ordinalp (osumf f n).
Proof.
move: n;apply: Nat_induction.
  by move => _; rewrite osum_f0; fprops.
move => n nN Hrec  /(true_below_rec nN) [/Hrec h1 h2].
rewrite (osum_fS _ nN); apply: (OS_sum2 h2 h1).
Qed.

Lemma OS_oprodf n f:
  natp n ->  ord_below f n ->
  ordinalp (oprodf f n).
Proof.
move: n;apply: Nat_induction.
  by move => _; rewrite oprod_f0; fprops.
move => n nN Hrec  /(true_below_rec nN) [/Hrec h1 h2].
rewrite (oprod_fS _ nN); apply: (OS_prod2 h1 h2).
Qed.

Lemma osumf_exten f g n: natp n -> same_below f g n ->
  osumf f n = osumf g n.
Proof.
move: n; apply: Nat_induction.
  by move => _; rewrite ! osum_f0.
move => n nN Hrec  /(true_below_rec nN) [/Hrec h1 h2].
by rewrite !(osum_fS _ nN) h1 h2.
Qed.

Lemma oprodf_exten f g n: natp n -> same_below f g n ->
  oprodf f n = oprodf g n.
Proof.
move: n; apply: Nat_induction.
  by move => _; rewrite ! oprod_f0.
move => n nN Hrec  /(true_below_rec nN) [/Hrec h1 h2].
by rewrite !(oprod_fS _ nN) h1 h2.
Qed.

Lemma osum_fA n m f:
  natp n -> natp m -> ord_below f (n +c m) ->
  osumf f (n +c m) =  (osumf (fun z => f (z +c n)) m) +o (osumf f n).
Proof.
move => nN mN; move: m mN n nN; apply: Nat_induction.
  move => n nN; rewrite (Nsum0r nN) (osum_f0) => fo.
  rewrite osum0l //; apply:OS_osumf => //.
move => m mN Hrec n nN.
have nmN:= NS_sum nN  mN.
rewrite (csum_nS _ mN) (osum_fS _ nmN).
move => /(true_below_rec nmN) [pa pb].
have pc:  ordinalp (osumf (fun z => f (z +c n)) m).
  apply: OS_osumf => // k km; apply: pa.
  by move: (csum_Mlteq nN km); rewrite csumC (csumC m). 
have pd:  ordinalp (osumf f n).
  apply: OS_osumf => // k km;apply: pa.
  exact:(clt_leT km (Nsum_M0le m nN)).
by rewrite Hrec // (osumA pb pc pd) (osum_fS _ mN) csumC.
Qed.

Lemma oprod_fA n m f:
  natp n -> natp m -> ord_below f (n  +c m) ->
  oprodf f (n +c m) =  (oprodf f n) *o (oprodf (fun z => f (z +c n)) m).
Proof.
move => nN mN; move: m mN n nN; apply: Nat_induction.
  move => n nN; rewrite (Nsum0r nN) (oprod_f0) => fo.
  rewrite oprod1r //; apply:OS_oprodf => //.
move => m mN Hrec n nN.
have nmN:= NS_sum nN mN.
rewrite (csum_nS _ mN) (oprod_fS _ nmN).
move => /(true_below_rec nmN) [pa pb].
have pc:  ordinalp (oprodf (fun z => f (z +c n)) m).
  apply: OS_oprodf => // k km; apply: pa.
  by move: (csum_Mlteq nN km); rewrite csumC (csumC m). 
have pd:  ordinalp (oprodf f n).
  apply: OS_oprodf => // k km; apply: pa.
  exact:(clt_leT km (Nsum_M0le m nN)).
by rewrite Hrec // - (oprodA pd pc pb) (oprod_fS _ mN) csumC.
Qed.

Lemma oprod_f1r p n: ord_below p (csucc n) -> natp n ->
    oprodf p (csucc n) = p \0c *o  oprodf (fun i => p (csucc i)) n. 
Proof.
move => obn nN.
move:(obn _ (succ_positive n)) => op0.
have ha: \1c +c n = csucc n by rewrite (Nsucc_rw nN) csumC.
rewrite - ha in obn.
rewrite - ha (oprod_fA NS1 nN obn) (oprod_f1 op0); apply: f_equal.
by apply:(oprodf_exten nN) => i lin; rewrite -(Nsucc_rw (NS_lt_nat lin nN)).
Qed.


Lemma osum_f1r p n: natp n -> ord_below p (csucc n) ->
    osumf p (csucc n) =  osumf (fun i => p (csucc i)) n +o p \0c. 
Proof.
move => nN ax.
have op0: ordinalp (p \0c) by apply: ax; apply: succ_positive.
move: ax;rewrite (Nsucc_rw nN) csumC => ax.
rewrite (osum_fA  NS1 nN ax) (osum_f1 op0); apply: f_equal2;last exact.
by apply: (osumf_exten nN) => i lin; rewrite (Nsucc_rw (NS_lt_nat lin nN)).
Qed.

(** ** Properties of ordering *)


Lemma olt_12: \1o <o \2o.
Proof. 
by move: olt_01 => /oltSSP; rewrite osucc_zero osucc_one.
Qed.

Lemma olt_02: \0o <o \2o.
Proof. exact: (olt_ltT olt_01 olt_12). Qed.

Lemma olt0S a: ordinalp a -> \0o <o (osucc a).
Proof. by move => oa; apply /oltSleP; apply: ole0x. Qed.
 
Lemma oge2P a: \2o <=o a <-> \1o <o a.
Proof.
rewrite - osucc_one;  apply:iff_sym; exact:oleSltP.
Qed.

Lemma ord2_trichotomy a: ordinalp a ->
  [\/ a = \0o, a = \1o | \2o <=o a].
Proof.
move=> oa.
case: (equal_or_not a \0o); first by constructor 1.
case: (equal_or_not \1o a); first by constructor 2.
by move => a1 a0; constructor 3; apply /oge2P; split =>//; apply: oge1.
Qed.

Lemma ord2_trichotomy1 a: \2o <=o a -> (a <> \0o /\ a <> \1o).
Proof.
move=> h; split; first exact: (nesym (proj2 (olt_leT olt_02 h))).
exact: (nesym (proj2 (olt_leT olt_12 h))).
Qed.

Lemma osum_Meqlt a b c:
  a <o b -> ordinalp c -> (c +o a) <o (c +o b).
Proof.
move => /oltP0 [oa ob ab] oc; apply /oltP; fprops.
rewrite (osum_rec_def oc ob); apply /setU2_P; right; apply/funI_P; ex_tac.
Qed.

Lemma oprod_Meqlt a b c:
  a <o b -> \0o <o c -> (c *o a) <o (c *o b).
Proof.
move => /oltP0 [oa ob ab] /oltP0 [oz oc zc]. 
apply /oltP; fprops; rewrite (oprod_rec_def oc ob); apply /funI_P.
exists (J \0o a); aww; rewrite osum0r; fprops.
Qed.

Lemma osum_Meqler a b c: ordinalp a -> ordinalp b -> ordinalp c ->
   c +o a <=o c +o b -> a <=o b.
Proof.
move => oa ob oc h.
case: (oleT_el oa ob) => // h1; case: (oleNgt h (osum_Meqlt h1 oc)).
Qed.

Lemma oprod_Meqler a b c: ordinalp a -> ordinalp b -> \0o <o c ->
   c *o a <=o c *o b -> a <=o b.
Proof.
move => oa ob oc h.
case: (oleT_el oa ob) => // h1;case: (oleNgt h (oprod_Meqlt h1 oc)).
Qed.

Lemma oprod2_pos a b: \0o <o a -> \0o <o b -> \0o <o a *o b.
Proof. by move => oa ob; move: (oprod_Meqlt ob oa); rewrite oprod0r. Qed.

Lemma oprod2_nz a b: ordinalp a -> ordinalp b ->
   a <> \0o -> b <> \0o -> a *o b <> \0o.
Proof.
move=> oa ob anz bnz.
exact:(nesym (proj2(oprod2_pos (ord_ne0_pos oa anz) (ord_ne0_pos ob bnz)))).
Qed.

Lemma osum_Meqle a b c:
  a <=o b -> ordinalp c -> (c +o a) <=o (c +o b).
Proof.
move => ab oc.
case: (equal_or_not a b) => nab.
  by rewrite nab; apply: oleR; apply: (OS_sum2 oc (proj32 ab)).
exact: (proj1 (osum_Meqlt (conj ab nab) oc)).
Qed.

Lemma oprod_Meqle a b c:
  a <=o b -> ordinalp c -> (c *o a) <=o (c *o b).
Proof.
move => ab oc.
case: (ozero_dichot oc) => cz.
   rewrite cz oprod0l oprod0l; apply: (oleR OS0).
case: (equal_or_not a b) => nab.
  by rewrite nab; apply: oleR; apply: (OS_prod2 oc (proj32 ab)).
exact: (proj1 (oprod_Meqlt (conj ab nab) cz)).
Qed.

(* deplacer et noter *)
Lemma ole_ltT_s a b c: ordinalp c -> a <=o b -> inc b c -> inc a c.
Proof.
by move => oc ab /(oltP oc) /(ole_ltT ab) bc; apply /(oltP oc). 
Qed.

Lemma osum_Mleeq a b c:
  a <=o b -> ordinalp c -> (a +o c) <=o (b +o c).
Proof.
move => ab; move: c; apply: least_ordinal2' => d od H. 
move: (ab) => [oa ob sab].
split; fprops; move:(OS_sum2 ob od). 
rewrite (osum_rec_def oa od)  (osum_rec_def ob od) => oh t;case /setU2_P. 
  by move => ta; apply/setU2_P; left; apply: sab.
move /funI_P => [z zd ->]; apply:(ole_ltT_s oh (H _ zd)).
apply/setU2_P; right; apply /funI_P; ex_tac.
Qed.

Lemma osum_Mle0 a b:
  ordinalp a -> ordinalp b -> a <=o (a +o b).
Proof.
move=> oa ob.
rewrite - {1} (osum0r oa); apply: osum_Meqle => //; apply:(ole0x ob).
Qed.

Lemma osum_M0le a b:
  ordinalp a -> ordinalp b -> b <=o (a +o b).
Proof.
move=> oa ob;rewrite - {1} (osum0l ob); apply: osum_Mleeq (ole0x oa) ob.
Qed.

Lemma osum_Mlele a b c d:
  a <=o b -> c <=o d -> (a +o c) <=o (b +o d).
Proof.
move=> le1 le2; apply: (oleT (osum_Meqle le2 (proj31 le1))).
apply:(osum_Mleeq le1 (proj32 le2)).
Qed.

Lemma oprod_Mleeq a b c:
  a <=o b -> ordinalp c -> (a *o c) <=o (b *o c).
Proof.
move => [oa ob sab]; move: c; apply: least_ordinal2' => d od H.
split; fprops.
rewrite (oprod_rec_def oa od) => t /funI_P [z /setX_P [_ p2 p3] ->].
apply: (ole_ltT_s (OS_prod2 ob od) (osum_Mleeq  (H _ p3) (Os_ordinal oa p2))).
rewrite (oprod_rec_def ob od); apply /funI_P; exists (J (P z) (Q z));aww.
Qed.

Lemma oprod_Mlele a b c d:
  a <=o b -> c <=o d -> (a *o c) <=o (b *o d).
Proof.
move=> le1 le2; apply: (oleT (oprod_Meqle le2 (proj31 le1))).
apply:oprod_Mleeq le1 (proj32 le2).
Qed.

Lemma oprod_Mle1 a b:
  ordinalp a -> \0o <o b -> a <=o (a *o b). 
Proof.
move=> oa /oge1P ba.
rewrite - {1} (oprod1r oa);exact: oprod_Mlele (oleR oa) ba.
Qed.

Lemma oprod_M1le a b:
  \0o <o a -> ordinalp b-> b <=o (a *o b).
Proof.
move=> /oge1P oa ob.
rewrite - {1} (oprod1l ob); exact: oprod_Mlele oa (oleR ob).
Qed.

Lemma oprod_Meq1lt b c:
  \1o <o b -> \0o <o c -> c <o (c *o b).
Proof.
move => lt1b cz.
rewrite - {1} (oprod1r (proj32_1 cz)); apply: (oprod_Meqlt lt1b cz).
Qed.

Lemma osum_Meqltr a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  (c +o a) <o (c +o b) -> a <o b.
Proof.
move => oa ob oc olt.
case: (oleT_el ob oa) => // oba.
case:(oltNge olt); exact: (osum_Mlele (oleR oc) oba).
Qed.

Lemma osum_Mlteqr a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  (a +o c) <o (b +o c) -> a <o b.
Proof.
move => oa ob oc olt.
case: (oleT_el ob oa) => // oba.
case: (oltNge olt); exact: (osum_Mlele oba (oleR oc)).
Qed.

Lemma oprod_Meqltr a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  (c *o a) <o (c *o b) -> a <o b.
Proof.
move => oa ob oc olt.
case: (oleT_el ob oa) => // oba.
case: (oltNge olt); exact: (oprod_Mlele (oleR oc) oba).
Qed.

Lemma oprod_Mlteqr a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  (a *o c) <o (b *o c) -> a <o b.
Proof.
move => oa ob oc olt.
case: (oleT_el ob oa) => // oba.
case: (oltNge olt); exact: (oprod_Mlele oba (oleR oc)).
Qed.

Lemma osum2_simpl a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  c +o a = c +o b -> a = b.
Proof.
move=> oa ob oc so.
by case: (oleT_ell oa ob) => h //;
   move: (osum_Meqlt h oc); rewrite so; move=> [_]; case. 
Qed.

Lemma oprod2_simpl a b c:
  ordinalp a -> ordinalp b -> \0o <o c ->
  c *o a = c *o b -> a = b.
Proof.
move=> oa ob oc eq.
by case: (oleT_ell oa ob) => h //;
   move: (oprod_Meqlt h oc); rewrite eq; move=> [_]; case. 
Qed.

Lemma oprod2_simpl1 a c: ordinalp a -> \0o <o c -> c *o a = c  -> a = \1o.
Proof.
move => sa sb.
rewrite -{2} (oprod1r (proj32_1 sb)) => sc.
by rewrite (oprod2_simpl sa OS1 sb sc).  
Qed.

Lemma osum2_a_ab a b:
  ordinalp a -> ordinalp b -> a +o b = a -> b = \0o.
Proof.
move => oa ob; rewrite - {2}(osum0r oa); apply: osum2_simpl; fprops.
Qed.

Lemma osum2_zero a b: ordinalp a -> ordinalp b ->
  a +o b = \0o -> (a = \0o /\ b = \0o).
Proof.
move=> oa ob s0; case: (ozero_dichot oa) => az.
  by rewrite -{2} s0 az (osum0l ob).
by case: (proj2(olt_leT az (osum_Mle0 oa ob))). 
Qed.

Lemma oprod2_one a b: ordinalp a -> ordinalp b ->
  a *o b = \1o -> (a = \1o /\ b = \1o).
Proof.
move=> oa ob ab1.
case: (equal_or_not a \1o) => a1.
  by move: ab1; rewrite a1 oprod1l.
case: (equal_or_not b \0c) => bz.
  by move: ab1; rewrite bz (oprod0r) => bad; case: card1_nz.
move: (ord_ne0_pos ob bz) => b1.
move: (oprod_Mle1 oa b1); rewrite ab1 => la2.
by move: ab1; rewrite (olt1 (conj la2 a1)) oprod0l => bad; case:card1_nz.
Qed.

Lemma oprod2_two a b: ordinalp a -> ordinalp b ->
  a *o b = \2o -> (a = \1o \/ b = \1o).
Proof.
move=> oa ob ab1.
case: (equal_or_not b \0c) => bz.
  by move: ab1; rewrite bz (oprod0r) => bad; case: card2_nz. 
have b1:= (ord_ne0_pos ob bz).
move: (oprod_Mle1 oa b1); rewrite ab1 => la2.
case:(ole_eqVlt la2) => a2.
  by right; apply: (oprod2_simpl ob OS1 olt_02); rewrite -{1}a2 (oprod1r OS2). 
move: a2; rewrite - osucc_one=>/oltSleP/ole_eqVlt; case; first by left.
move/olt1 => az.
by move: ab1; rewrite az (oprod0l) => bad; case: card2_nz.
Qed.


Lemma osum2_succ x y: 
   ordinalp x -> ordinalp y -> osucc (x +o y) = x +o (osucc y).
Proof.
move=> oa ob.
rewrite -(osucc_pr ob) (osumA oa ob OS1) osucc_pr ;fprops.
Qed.

Lemma oprod2_succ a b: ordinalp a -> ordinalp b ->
   a *o (osucc b) =  (a *o b) +o a.
Proof.
move=> oa ob. 
rewrite -(osucc_pr ob)  (oprodD ob OS1 oa); rewrite oprod1r //. 
Qed.

Lemma oprod2_nsucc a b: ordinalp a -> ordinalp b ->
  a +o (a *o b) = a *o (\1o +o b).
Proof. move: OS1=> o1 ox oy; rewrite oprodD // oprod1r //. Qed.

Lemma osum_fnz n X: natp n ->  ord_below X n -> 
   (exists2 i, i <c n & X i <> \0o) -> \0o <o osumf X n.
Proof.
move => nN ax [i]; move: n nN ax.
apply:Nat_induction; first by move => _ /clt0.
move => n nN Hr ax /(cltSleP nN)/cle_eqVlt  lin inz.
move: (true_below_rec nN ax) => [ax1 axb].
move: (OS_osumf (NS_succ nN) ax) => o1.
move: (OS_osumf nN ax1) => o2.
apply: (ord_ne0_pos o1); rewrite (osum_fS _ nN) => /(osum2_zero axb o2).
move => [ha hb].
case: lin => lin; first by case: inz; rewrite lin.
by move: (proj2(Hr ax1 lin inz)); rewrite hb.
Qed.



Lemma osum_Mon1 f n i: natp n -> i <c n -> ord_below f n ->
   f i <=o osumf f n.
Proof.
move:n; apply: Nat_induction; first by move => /clt0.
move => n nN Hrec /(cltSleP nN) /cle_eqVlt lin axs.
move:(true_below_rec nN axs) => [axn ax1].
rewrite (osum_fS _ nN).
case:lin; first by  move ->; exact:(osum_Mle0 ax1 (OS_osumf nN axn)) => le1.
move => lin; exact: (oleT (Hrec lin axn) (osum_M0le ax1 (OS_osumf nN axn))).
Qed.

Lemma osum2_2int a b:
  natp a -> natp b -> a +o b = a +c b.
Proof.
move=> aN bN;move: b bN.
have oa:= OS_nat aN.
apply: Nat_induction; first by rewrite  (Nsum0r aN) (osum0r oa).
move=> n nN hrec.
rewrite (csum_nS _ nN)  (succ_of_nat nN) (succ_of_nat (NS_sum aN nN)).
by rewrite - (osum2_succ oa (OS_cardinal (CS_nat nN))) hrec.
Qed.

Lemma oprod2_2int a b:
  natp a -> natp b -> a *o b = a *c b.
Proof.
move=> aN bN;move: b bN.
have oa:= OS_nat aN.
apply: Nat_induction; first by rewrite cprod0r  oprod0r.
move=> n nN hrec.
rewrite (cprod_nS _ nN) (succ_of_nat nN) - (osum2_2int  (NS_prod aN nN) aN).
by rewrite  (oprod2_succ oa (OS_cardinal (CS_nat nN))) hrec.
Qed.

Lemma osum2_lt_omega a b:
   a <o omega0 -> b <o omega0 -> (a +o b) <o omega0. 
Proof. 
move /olt_omegaP => aN /olt_omegaP bN; apply /olt_omegaP.
rewrite osum2_2int; fprops.
Qed.

Lemma oprod2_lt_omega a b: 
   a <o omega0 -> b <o omega0 -> (a *o b) <o omega0. 
Proof. 
move /olt_omegaP => aN /olt_omegaP bN;apply /olt_omegaP.
rewrite oprod2_2int; fprops.
Qed.

Lemma osum_11_2: \1o +o \1o = \2o.
Proof. by rewrite (osum2_2int NS1 NS1) csum_11. Qed.

Lemma ord_double a:
  ordinalp a -> a *o \2o = a +o a.
Proof.
by move=> ox; rewrite - osum_11_2 (oprodD OS1 OS1 ox) (oprod1r ox).
Qed.

Lemma osum_int_omega n:
  n <o omega0 -> n +o omega0 = omega0.
Proof.
move => no; move: (no) => [[on oo son] _].
set_extens t; last by apply: (proj33 (osum_M0le on oo)).
rewrite (osum_rec_def on oo); case /setU2_P; first by apply: son.
move => /funI_P [z zo ->]; apply /(oltP oo) /(osum2_lt_omega no).
by apply/(oltP oo).
Qed.

Lemma oprod_int_omega n:
  n <o omega0 -> \0c <o n -> n *o omega0 = omega0.
Proof.
move => no np; move: (no) => [[on oo son] _].
set_extens t; last by apply: (proj33 (oprod_M1le np oo)).
rewrite (oprod_rec_def on oo) => /funI_P [z /setX_P [z1 z2 /(oltP oo) z3] ->].
apply /(oltP oo) /(osum2_lt_omega).
  by apply (oprod2_lt_omega no z3).
by apply/(oltP oo); apply: son.
Qed.

Lemma osum2_nc (a := \1o) (b := omega0):
   a +o b <> b +o a.
Proof.
rewrite (osum_int_omega olt_1omega) /b=> h.
symmetry in h; move: (osum2_a_ab OS_omega OS1 h);apply:card1_nz.
Qed.

Lemma oprod2_nc (a := \2o) (b := omega0):
  a *o b <> b *o a.
Proof.
rewrite (oprod_int_omega olt_2omega olt_02) (ord_double OS_omega) => /esym h.
move: (osum2_a_ab OS_omega OS_omega h); apply: omega_nz.
Qed.

Lemma osum2_nD (a:= \1o) (b:= \1o) (c:= omega0):
  (a +o b) *o c <> (a *o c) +o (b *o c).
Proof.
rewrite (oprod_int_omega olt_1omega olt_01) (osum2_2int NS1 NS1).
rewrite csum_11 (oprod_int_omega olt_2omega olt_02) => /esym h.
move: (osum2_a_ab OS_omega OS_omega h).
apply: omega_nz.
Qed.

Lemma cardinal_of_ordinal r:
  worder r -> (ordinal r) =c (substrate r).
Proof.
move=> wor; symmetry;apply /card_eqP.
move: (ordinal_o_is wor) => [f [o1 o2 [bf pa pb] pc]].
by exists f; split => //; rewrite pb ordinal_o_sr.
Qed.


Lemma osum_cardinal a b:
  ordinalp a -> ordinalp b -> 
  cardinal (a +o b) = (cardinal a) +c (cardinal b).
Proof.
move => ox oy; symmetry.
rewrite /osum2.
set w := order_sum2 _ _.
have w1: worder w by rewrite /w;fprops.
have pa:= (OS_ordinal w1).
move: (ordinal_o_is w1) => [F [_ _ [bf sf tf] _]].
have /card_eqP: source F \Eq target F by exists F.
rewrite tf (ordinal_o_sr (ordinal w)) sf {1} /w orsum2_sr; fprops.
rewrite (ordinal_o_sr a)(ordinal_o_sr b) => <-.
rewrite /canonical_du2 -/(csum _)  csum_pr; apply: csum2_pr; aw.
set f := fun a:Set => _.
by move: (doubleton_fam_canon f); rewrite /f;aw.
Qed.

Lemma oprod_cardinal a b:
  ordinalp a -> ordinalp b -> 
  cardinal (a *o b) = (cardinal a) *c (cardinal b).
Proof.
move => xo yo.
have wox:= (ordinal_o_wor xo).
have woy:= (ordinal_o_wor yo).
have orx := (ordinal_o_or a).
have ory := (ordinal_o_or b).
have pa: worder (order_prod2 (ordinal_o a) (ordinal_o b)) by fprops.
rewrite /oprod2 (cardinal_of_ordinal pa) (orprod2_sr orx ory).   
rewrite (ordinal_o_sr a)  (ordinal_o_sr b) cprod2cl cprod2cr cprodC.
symmetry;rewrite cprod2_pr1;  apply /card_eqP.
exists (product2_canon b a); split => //.
- apply: product2_canon_fb.
- by rewrite /product2_canon; aw.
- by rewrite /product2_canon; aw.
Qed.


Lemma osum_cardinal_gen r X:
  worder_on r (domain X) -> ordinal_fam X ->
  cardinal (osum r X) = csumb (domain X) (fun z => cardinal (Vg X z)).
Proof.
move => sa sb.
set Y := (Lg (domain X) (fun z => ordinal_o (Vg X z))).
have hb: worder_fam Y.
  rewrite /Y /worder_fam /allf Lgd.
  move => i idx;rewrite LgV //; apply: ordinal_o_wor; apply:(sb _ idx).
have hc:worder (order_sum r Y) by apply:orsum_wor; rewrite /Y; aw.
have hd:orsum_ax r Y.
  move: sa => [[or _]dr].
  have sr:substrate r = domain Y  by rewrite /Y; aw.
  by split => // i /hb [].
rewrite /osum -/Y (cardinal_of_ordinal hc) (orsum_sr hd).
rewrite /sum_of_substrates -/(csum _) csum_pr /fam_of_substrates /Y !Lgd.
  by apply: csumb_exten => i idx; rewrite !LgV //ordinal_o_sr.
Qed.


Lemma finite_rems c: ordinalp c ->
  finite_set (Zo (osucc c) (fun b => exists2 a, ordinalp a & c = a +o b)).  
Proof.
move => oc; set E := Zo _ _.
pose p b a := ordinalp a /\ c = a +o b.
pose Eb b := Zo (osucc c) (p b).
have Pa: forall b, inc b E -> nonempty(Eb b).
  move => b/Zo_P [/(oleP oc) ha [a oa hc]]; exists a => //; apply:Zo_i => //.
  apply/(oleP oc); rewrite hc; apply:(osum_Mle0 oa (proj31 ha)).
have Pb: forall b, ordinal_set (Eb b) by  move => b a /Zo_hi [].
pose f b := intersection (Eb b).
have Pc: forall b, inc b E -> inc (f b) (Eb b).
  move => b /Pa h; apply:ordinal_setI => //.
have CP: forall b, inc b E -> p b (f b) by move => b /Pc /Zo_hi. 
have ci: forall a b, inc a E -> inc b E -> a <o b -> f b <o f a.
  move => a b /CP [ofa s1] /CP [ofb s2] lab.
  case: (oleT_el ofa ofb) => // la.
  move: (osum_Meqlt lab ofa); rewrite - s1 => /oltNge; case.
  by move:(osum_Mleeq la (proj32_1 lab)); rewrite - s2.
have ose: ordinal_set E by move => t /Zo_S /(Os_ordinal (OS_succ oc)).
pose F := fun_image E f.
have osf: ordinal_set F by move => t /funI_P [z /CP [osf _] -> ].
move:(wordering_ole_pr ose) => [ha hb].
move:(wordering_ole_pr osf) => [hc hd].
have he: forall i, inc i (substrate (ole_on E)) -> 
  inc (f i) (substrate (ole_on F)).
  move =>i; rewrite hb hd => ie; apply/funI_P; ex_tac.
have hf:forall i j, glt (ole_on E) i j -> glt (ole_on F) (f j) (f i).
  move => i j [/graph_on_P1 [ie je lij] nij].
  move: (ci _ _ ie je (conj lij nij)) => [lfij nfij].
  split => //; apply/graph_on_P1; split => //; apply/funI_P; first by exists j.
  by exists i.
by move: (worder_decreasing_finite ha hc he hf); rewrite hb.
Qed.

Section InfiniteNormal.
Variable C: Set.
Hypothesis iC: infinite_c C.
Let E := (cnext C).

Lemma cnext_sum x y: inc x E -> inc y E -> inc (x +o y) E.
Proof.
move: iC => [cc _].
move=> /(cnextP cc) [xo cx] /(cnextP cc) [yo cy].
apply /(cnextP cc);split; first by fprops.
rewrite osum_cardinal //.
move: (csum_Mlele cx cy); rewrite csum_inf1 //; apply /infinite_setP. 
Qed.

Lemma cnext_prod x y: inc x E -> inc y E -> inc (x *o y) E.
Proof.
move: iC => [cc _].
move=> /(cnextP cc) [xo cx] /(cnextP cc) [yo cy].
apply /(cnextP cc);split; first by fprops.
move: (cprod_Mlele cx cy); rewrite oprod_cardinal // csquare_inf //. 
Qed.


Lemma cnext_leomega x: x <=o omega0 -> inc x E.
Proof.
move: iC => [cc _].
move => [ox oo xo]; apply /(cnextP cc); split =>  //.
have: cardinal x <=c cardinal Nat by apply: sub_smaller.
rewrite cardinal_Nat;move /infinite_c_P2: iC => h1 h2; apply: cleT h2 h1.
Qed.

Lemma cnext_zero: inc \0o E.
Proof. exact: (cnext_leomega (proj1 olt_0omega)). Qed.

Lemma cnext_succ x: inc x E -> inc (osucc x) E.
Proof.
move=> cx; move/(cnextP (proj1 iC)):(cx) => [ox _]. 
rewrite - (osucc_pr ox); move: olt_1omega => [h _].
by apply: cnext_sum => //; apply:cnext_leomega.
Qed.

Lemma cnext_sup F: cardinal F <=c C -> sub F E -> inc (\osup F) E.
Proof.
move: (iC) => [cc _]pa pb; apply/(cnextP cc); split.
  by apply: OS_sup => t/pb /cnextP [].
rewrite - setUb_identity.
move: (csum_pr1 (identity_g F)); rewrite identity_d /csumb;set f := Lg _ _.
have cdf: cardinal (domain f) <=c C by rewrite /f; aw.
have etc: forall i, inc i (domain f) -> Vg f i <=c C.
  rewrite /f; aw; move => i idf. rewrite LgV // identity_ev //.
  by move /cnextP: (pb _ idf) => [].
move: (notbig_family_sum iC cdf etc) => ha hb; exact :cleT hb ha.
Qed.

End InfiniteNormal.

Lemma cnext_pred c:  cardinalp c ->  c = \csup (Zo (cnext c) cardinalp).
Proof.
move => cc.
have oc:= (proj1 cc).
set E := (Zo (cnext c) cardinalp).
have cse: (cardinal_set E) by move => t /Zo_P [].
have pa: inc c E.
   apply /Zo_P; split=> //; apply /(cnextP cc) => //.
   rewrite card_card //; split; fprops.
apply:(cleA (card_sup_ub cse pa)).
apply:(card_ub_sup cc).
by move => x /Zo_P [ /(cnextP cc) [ox h]] /card_card <-.
Qed.

Lemma cnext_pred_more E (c:= \csup (Zo E cardinalp)):
  (exists2 C, infinite_c C & E = cnext C) ->
  infinite_c c /\ E = cnext c.
Proof.
move => [C pa pb].
by move:(cnext_pred (proj1 pa)); rewrite - pb -/c => <-.
Qed. 


Definition aleph_one := cnext omega0.

Definition countable_ordinal a := ordinalp a /\ countable_set a.

Lemma aleph_oneP a: inc a aleph_one <-> countable_ordinal a.
Proof.
move:(cnextP CS_omega) => h.
split; first by move/h => [ha /countableP hb]. 
by move => [ha /countableP hb]; apply/h.
Qed.

Lemma osum2_countable a b:
  countable_ordinal a -> countable_ordinal b -> countable_ordinal (a +o b).
Proof.
move: CIS_omega aleph_oneP => h T.
by move => /T xa /T xn; apply /T;apply:cnext_sum.
Qed.

Lemma oprod2_countable a b:
   countable_ordinal a -> countable_ordinal b -> countable_ordinal (a *o b).
Proof.
move: CIS_omega aleph_oneP => h T.
by move => /T xa /T xn; apply /T;apply:cnext_prod.
Qed.

Lemma countable_ordinal_sup E: 
  countable_set E -> (alls E countable_ordinal)->
  countable_ordinal (\osup E).
Proof.
move: CIS_omega aleph_oneP => h T.
move => /countableP pa pb.
have se:sub E aleph_one by move => t /pb /T.
by move /T: (cnext_sup h pa se).
Qed.


Lemma countable_leomega a:
  a <=o omega0 ->  countable_ordinal a.
Proof. move => [ox oo /countable_sub_Nat xo]; split => //. Qed.


Lemma countable_one: countable_ordinal \1o.
Proof. move: olt_1omega => [o1 _]; by apply: countable_leomega. Qed. 

Lemma countable_succ a:
   countable_ordinal a -> countable_ordinal (osucc a).
Proof.
move=> cx; move: (cx) => [ox _]; rewrite - (osucc_pr ox).
apply: osum2_countable => //; apply: countable_one.
Qed.

Lemma cardinal_omega2: cardinal omega0 = cardinal (omega0 +o omega0).
Proof.
move: OS_omega => o_o.
rewrite osum_cardinal // csum_inf1 // (card_card CS_omega).
exact:CIS_omega. 
Qed.

(** ** Least upper bound *)
 
Definition ord_cofinal x y := 
  sub x y /\ forall a, inc a y -> exists2 b, inc b x & a <=o b.

Definition mutually_cofinal x y :=
   (forall a, inc a x -> exists2 b, inc b y & a <=o b) /\
   (forall a, inc a y -> exists2 b, inc b x & a <=o b).


Lemma ord_ub_sup1 a X: ordinalp a -> sub X a -> \osup X <=o a.
Proof.
by move => oa Xa; apply: ord_ub_sup => // t /Xa /(oltP oa) [].
Qed.

Lemma ord_sup_ordinal a (b:= \osup a): ordinalp a ->
  a = b \/ a = osucc b.
Proof.
by move=> oa; case: (osuccVpred oa); [  move/predo_K; right | left ].
Qed.

Lemma ord_sup_sub X: 
  ordinal_set X ->  ~ (inc (\osup X) X) ->
  forall x, inc x X -> x <o (\osup X).
Proof.
by move=> h1 h2 x xX; split; [apply: ord_sup_ub | dneg xs; rewrite -xs ].
Qed.


Lemma oset_sub_ordinal X: ordinal_set X -> sub X (osucc (\osup X)).
Proof.
move => ose t tX.
by apply/(ordinal_sub4P (ose t tX) (OS_sup ose)); apply: (setU_s1 tX).
Qed.

Lemma ord_sup_sub' X: 
  ordinal_set X ->  (inc (\osup X) X) \/ sub X (\osup X).
Proof.
move/oset_sub_ordinal => XS; case:(inc_or_not (\osup X) X) => h; first by left.
right => t tX; case/setU1_P: (XS _ tX) => // tu; case:h; ue.
Qed.

Lemma ord_sup_inVlimit  X: 
  ordinal_set X -> nonempty X -> 
  inc (\osup X) X \/ limit_ordinal (\osup X).
Proof.
move=> alo [a aX].
case: (p_or_not_p (inc (\osup X) X)) => nsX; [ by left | right].
have asu:= (ord_sup_ub alo aX).
have so:= proj32 asu.
case: (ordinal_limA so) => //.
  by move=> h; rewrite h in nsX asu;case: nsX; rewrite - (ole0 asu).
move =>  [y oy h].
have aiy: (forall i, inc i X -> i <=o y).
  move=> i iX; apply /oltSleP. 
  by rewrite -h; apply: ord_sup_sub.
move: (ord_ub_sup oy aiy); rewrite h.
by move /oleSltP => [_ ?].
Qed. 

Lemma ord_sup_M x y: 
  sub x y -> ordinal_set y -> (\osup x) <=o (\osup y).
Proof.
move=> xy al1.
apply:ord_ub_sup => //; first by apply: OS_sup.
by move=> i ix; apply: ord_sup_ub => //; apply: xy.
Qed.

Lemma ord_sup_2cofinal x y: 
  mutually_cofinal x y -> \osup x = \osup y.
Proof.
move=> [p3 p4].
have osx: ordinal_set x by move => a ax; move: (p3 _ ax) => [b _ []].
have osy: ordinal_set y by move => a ay; move: (p4 _ ay) => [b _ []].
apply: oleA.
  apply: ord_ub_sup => //; first by apply: OS_sup.
  move=> i ix; move: (p3 _ ix) => [j jy lij]. 
  apply: (oleT lij);apply ord_sup_ub => //.
apply: ord_ub_sup => //; first by apply: OS_sup.
move=> i ix; move: (p4 _ ix) => [j jy lij]. 
apply: (oleT lij);apply: ord_sup_ub => //.
Qed.

Lemma ord_sup_2funI X f g:
  {inc X, f =1 g} ->
  \osup (fun_image X f) = \osup (fun_image X g).
Proof.
move=> h; congr union.
set_extens t; move /funI_P => [z zX ->]; apply /funI_P;ex_tac.
by symmetry; apply: h.
Qed.

Lemma ord_sup_1cofinal x y:
  ord_cofinal x y  ->  ordinal_set y -> \osup x = \osup y.
Proof.
move=> [h1 h2] h3; apply: ord_sup_2cofinal; split => // a ay;exists a;fprops.
Qed.

Lemma olt_sup  A x: ordinal_set A -> x <o (\osup A) ->
  exists2 z, inc z A & x <o z.
Proof.
move=> osA h.
have ox:= proj31_1 h.
ex_middle bad.
have: (forall z, inc z A -> z <=o x).
  move => z zA;case:(oleT_el  (osA _ zA) ox) => // xz; case: bad; ex_tac.
move => pc;case: (oltNge h (ord_ub_sup ox pc)).
Qed.

Lemma clt_sup A x: 
  cardinal_set A -> x <c \csup A -> exists2 z, inc z A & x <c z.
Proof.
move => p1 p2.
have q1:= oset_cset p1.
move: (oclt p2) => q2.
move: (olt_sup q1 q2) => [z zA zlt];  ex_tac.
exact (oclt3 (proj31_1 p2) (p1 _ zA) zlt).
Qed.

Lemma ord_cofinal_p1 A B: ordinal_set B -> 
   (ord_cofinal A B <-> cofinal (ole_on B) A).
Proof.
move => h.
have pa: (substrate (ole_on B)) = B.
  rewrite graph_on_sr // => c /h oc; fprops.
split. 
  move => [sa sb]; hnf; rewrite pa; split => //.
  move => x xb; move: (sb _ xb) => [y ya xy]; exists y => //.
  by apply /graph_on_P1; split => //; apply: sa.
rewrite /cofinal pa; move  => [sa sb]; split => // x xb.
move:(sb _ xb) => [y ya /graph_on_P1 [_ yb yx]]; ex_tac.
Qed.

Lemma ord_cofinal_p2 A B: limit_ordinal B -> sub A B ->
   (ord_cofinal A B <-> \osup A = \osup B).
Proof.
move => pa pb; move: (pa) => [ob _ _]; split.
  by move => [_ pc]; apply: ord_sup_1cofinal => // x /(Os_ordinal ob).
move => pc; split => // x xb.
have ox:=(Os_ordinal ob xb).
have osa:= (Os_sub (Os_ordinal ob) pb).
ex_middle h.
have pd: forall y, inc y A -> y <o x.
   move => y ya.
   case (oleT_el ox (osa _ ya)) => // pe; case h; ex_tac.
have sb: \osup B <=o x by rewrite - pc; apply: ord_ub_sup => // i /pd [].
move: xb sb. 
by rewrite -[union B](limit_nonsucc pa); move /(oltP ob) => ua /(oltNge ua).
Qed.

Lemma ord_cofinal_p3 a: limit_ordinal a ->
  (\osup a = \osup  (osucc a) /\  ~(ord_cofinal a (osucc a))).
Proof.
move => la; move: (la) => [oa _ _].
rewrite - [union a](limit_nonsucc la).
split; first by rewrite [union _] succo_K.
move => [h1 h2].
have: inc a (osucc a) by rewrite /osucc; fprops.
by move/h2 => [y /(oltP oa) ya] /(oltNge ya).
Qed.

Lemma ord_cofinal_p4 A C (E:= cnext C): infinite_c C ->
  ord_cofinal A E -> cardinal A = E.
Proof.
move => sa [sb sc].
have [pa pb pc] := (cnext_pr1 (proj1 sa)).
have ose:= (Os_ordinal (proj1 pa)).
case: (cleT_el (CS_cardinal A) (proj1 sa)); last first.
  move /pc; move: (sub_smaller sb);rewrite (card_card pa);exact:cleA.
move => cyc; move: (cnext_sup sa cyc sb)=> xsb.
have sse:= (ord_sup_1cofinal (conj sb sc) ose).
have hy:= (infinite_card_limit2( cle_inf_inf sa (proj1 pb))).
have ue:=(limit_nonsucc hy).
by move: (ordinal_irreflexive (proj1 pa)); rewrite {1} ue -[opred _] sse.
Qed.

Lemma ord_cofinal_p5 A C (E:= cnext C): infinite_c C ->
  ord_cofinal A E -> ordinal (ole_on A) = E.
Proof.
move => pa pc; move: (proj1 pc) => pb.
have ca:= (ord_cofinal_p4 pa pc).
set x := ordinal (ole_on A).
have [sa sb sc] := (cnext_pr1 (proj1 pa)).
have osa:=(Os_sub (Os_ordinal (proj1 sa)) pb).
have [pe pf]:=(wordering_ole_pr osa).
move: (cardinal_of_ordinal pe); rewrite pf -/x ca => cc.
have [oe hh] : cardinalp E by exact: (proj32_1 sb).
have ox: ordinalp x by apply: OS_ordinal.
have cc2: E \Eq x by apply /card_eqP; symmetry; rewrite cc -/E card_card.
apply: oleA; last by split => //;exact: (hh _ ox cc2).
apply/ordinal_le_P0; split=> //.
move: (the_ordinal_iso1 pe); rewrite -/x.
have o1 :=(proj1 (ordinal_o_wor oe)).
have o2 := (proj1 pe).
have o3:order (ordinal_o x) by fprops.
set f := (the_ordinal_iso _) => ff.
rewrite /order_le; split => //; rewrite ordinal_o_sr; exists f, A; split => //.
have -> //: (induced_order (ordinal_o E) A =  (ole_on A)).
have aso :sub A (substrate (ordinal_o E)) by rewrite ordinal_o_sr.
have [sd se]:= (iorder_osr o1 aso).
apply: order_exten => // u v; split.
   move /iorder_gleP => [ua va /ordo_leP [_ _ ha]]; apply /graph_on_P1. 
   split => //; split => //; fprops.
move => /graph_on_P1[ua ub [_ _ uv]]; apply /iorder_gleP; split => //.
apply/ordo_leP;split => //; fprops.  
Qed.


(** **  Subtraction *)
Definition odiff b a := Zo b (fun z => inc (a +o z) b).

Notation "x -o y" := (odiff x y) (at level 50).

Lemma OS_diff a b: ordinalp a -> ordinalp b -> ordinalp (b -o a).
Proof.
move => oa ob.
apply: ordinal_pr; last by move => t /Zo_S /(Os_ordinal ob).
move => u /Zo_P [ub /(oltP ob) ss] t tu.
apply: (Zo_i (ordinal_transitive ob ub tu)). 
apply /(oltP ob); apply: ole_ltT ss; apply:osum_Meqle => //.
by move/(oltP (Os_ordinal ob ub)): tu => [].
Qed.

Lemma odiff_wrong a b: b <=o a -> b -o a = \0o.
Proof.
move => ba; move: (ba) => [ob oa _]; apply /set0_P.
move => t /Zo_P [tb /(oltP ob) s1].
exact: (oltNge (olt_leT s1 ba) (osum_Mle0 oa (Os_ordinal ob tb))).
Qed.

Lemma odiff_Mle a b: ordinalp a -> ordinalp b ->  (b -o a) <=o b.
Proof.
move => oa ob; split; [ exact:(OS_diff oa ob) | exact | apply: Zo_S].
Qed.

Lemma odiff_pr a b: a <=o b ->
  (ordinalp (b -o a) /\ b = a +o (b -o a)).
Proof.
move => ab;move: (ab) => [oa ob sab]; split; first exact: (OS_diff oa ob).
move: b ob sab {ab}; apply: least_ordinal2' => d od H sad.
rewrite (osum_rec_def oa (OS_diff oa od)); set_extens t; last first.
  case/setU2_P; [ apply: sad | by move /funI_P => [z /Zo_hi za ->]].
move => td; apply/setU2_P; case: (oleT_el oa (Os_ordinal od td)).
  move => [_ _ /(H _ td)] h.
  right; apply /funI_P. exists (t -o a) => //; apply:Zo_i; last by ue.
  exact:(ole_ltT_s od (odiff_Mle oa (Os_ordinal od td)) td).
by move /(oltP oa); left.
Qed.

Lemma odiff_pr2 a b c: 
  ordinalp a -> ordinalp b -> ordinalp c -> 
  (a +o c = b) -> c = b -o a.
Proof.
move => oa ob oc h.
have lab: a<=o b by rewrite -h; exact :(osum_Mle0 oa oc).
have [pa pb]:= (odiff_pr lab).
rewrite pb in h; exact: (osum2_simpl oc pa oa h). 
Qed.

Lemma odiff_pos  a b: a <o b -> \0o <o (b -o a).
Proof.
move=> [leab bab]; move: (odiff_pr leab) => [xx eq].
by apply :ord_ne0_pos => // h; case: bab; rewrite eq h (osum0r (proj31 leab)).
Qed.


Lemma odiff_pr1 a b: ordinalp a -> ordinalp b -> (a +o b) -o a = b.
Proof.
move=> oa ob.
have [so sp] := (odiff_pr (osum_Mle0 oa ob)).
by move: (osum2_simpl ob so oa sp).
Qed.


Lemma osum_1inf a: omega0 <=o a -> \1o +o a = a.
Proof.
move => pa; move: (odiff_pr pa) => [pb pc]; rewrite pc.
by rewrite (osumA OS1 OS_omega pb) (osum_int_omega olt_1omega).
Qed.

Lemma oadd1_fix a: ordinalp a -> (\1o +o a = a <-> omega0 <=o a).
Proof.
move => ox; split; last by apply:osum_1inf.
move => h; case: (oleT_el OS_omega ox) => // /olt_omegaP xN.
move: (osum2_2int NS1 xN); rewrite h csumC - (Nsucc_rw xN).
by move: xN => /NatP /finite_cP [_].
Qed.

Lemma odiff_1inf a: omega0 <=o a -> a -o \1o = a.
Proof.
move => h; rewrite -{1} (osum_1inf h)  odiff_pr1;fprops; exact: (proj32 h).
Qed.

Lemma odiff_pr1_wrong a: omega0 <=o a -> (a +o \1o) -o \1o <> a.
Proof.
move => h.
have op:= proj32 h.
move: (oltS op) => [l1 /nesym l2].
by rewrite (osucc_pr op) (odiff_1inf (oleT h l1)).
Qed.

Lemma oprec_nat n: \0o <o n -> n <o omega0 ->  n = osucc (n -o \1o).
Proof.
move => xnz xo.
have pa: \1o <=o n by apply/ oge1P.
have [sa sb]:= (odiff_pr pa).
move: (osum_M0le OS1 sa); rewrite - sb => sc; move: (ole_ltT sc xo) => yo.
have sd: inc (n -o \1o) omega0 by case/oltP0: yo.
rewrite - (osucc_pr sa) {1} sb.
by rewrite (osum2_2int NS1 sd) (osum2_2int sd NS1) csumC.
Qed.

Lemma oprec_nat2 n: \0o <o n -> n <o omega0 -> 
  (osucc n -o \1o) = osucc (n -o \1o).
Proof.
move => xz cox.
have ox:= proj32_1 xz.
have xb: inc n omega0 by case/oltP0: cox.
rewrite -(oprec_nat xz cox);symmetry;apply:(odiff_pr2 OS1 (OS_succ ox) ox).
by rewrite (osum2_2int NS1 xb) csumC -(osum2_2int xb NS1) (osucc_pr ox).
Qed.

Lemma oprec_Mlt a b: \0o <o a -> a <o b -> (a -o \1o) <o (b -o \1o).
Proof.
move => ap ab.
have [[oa  ob _] _ ] := ab.
case: (oleT_el OS_omega oa) => af.
 by rewrite (odiff_1inf af) (odiff_1inf (oleT af (proj1 ab))).
case: (oleT_el OS_omega ob) => bf.
  rewrite (odiff_1inf bf); apply: olt_leT bf.
  exact: (ole_ltT (odiff_Mle OS1 oa) af).
apply /oltSSP.
by rewrite - (oprec_nat ap af) - (oprec_nat (olt_leT ap (proj1 ab)) bf).
Qed.


(** ** Ordinal division *)


Definition sincr_ofs (f: fterm) := 
  (forall x y, x <o y -> (f x) <o (f y)).

Lemma sincr_bounded_unique h y y' a:
   sincr_ofs h -> ordinalp y -> ordinalp y' ->
   (h y) <=o a -> a <o h (osucc y)  ->
   (h y') <=o a -> a <o (h (osucc y'))  ->
   y = y'.
Proof.
move=> oih oy oy' le1 le2 le3 le4.
wlog: y y' oy oy' le1 le2 le3 le4 / y <o y'.
  case: (oleT_ell oy oy') => // ll;  first by apply.
  by move=> aux;symmetry; apply: aux.
have lt2:=(ole_ltT le3 le2).
move /oleSltP => h2.
case: (equal_or_not (osucc y) y').
  by move=> h3; move: lt2=> [_]; rewrite h3. 
move=> h3; have h4: (osucc y) <o y' by split.
move: (oih _ _ h4) => [/(oltNge lt2) []].
Qed.


Definition odiv_pr0 a b q r :=
  [/\ ordinalp q, ordinalp r, a = (b *o q) +o r & r <o b].

Definition odiv_pr1 a b c q r :=
  odiv_pr0 a b q r /\ q <o c.

Definition oquorem a b := 
   select (fun z => a = b *o (P z) +o (Q z)) ((osucc a) \times b).
Definition oquo a b := P (oquorem a b).
Definition orem a b := Q (oquorem a b).

Lemma odivision_unique a b q r q' r':
  ordinalp a -> ordinalp b  ->
  odiv_pr0 a b q r -> odiv_pr0 a b q' r' ->
  (q = q' /\ r = r').
Proof.
move => oa ob pa pb.
have aux: forall q r, 
  odiv_pr0 a b q r -> (b *o q <=o a /\ a <o b *o (osucc q)).
  move=> q1 r1 [oq or -> rb]; rewrite (oprod2_succ ob oq).
  split; first by apply:(osum_Mle0 (OS_prod2 ob oq) or).
  apply:(osum_Meqlt rb (OS_prod2 ob oq)).
move: (aux _ _ pa) (aux _ _ pb) => [s1 s2] [s3 s4].
pose h y := b *o y.
move: pa pb => [oq or e1 rb] [oq' or'  e2 _].
have bp:= (ole_ltT (ole0x or) rb).
have sii: sincr_ofs (oprod2 b).
  by move => u v uv; apply: oprod_Meqlt.
move: (sincr_bounded_unique sii oq oq' s1 s2 s3 s4).
move => sq; split => //; rewrite e1 sq in e2.
exact: (osum2_simpl or or' (OS_prod2 ob oq') e2).
Qed.


Lemma odivision_exists a b c:
  ordinalp b -> ordinalp c ->  a <o (b *o c) ->
  odiv_pr1 a b c (oquo a b) (orem a b).
Proof.
move =>  ob oc lac.
have oa := (proj31_1 lac).
have osa :=  (OS_succ oa).
case: (ozero_dichot ob) => bp; first by move: lac; rewrite bp oprod0l => /olt0.
pose p z := a = b *o (P z) +o (Q z).
move /(oltP (OS_prod2 ob oc)):lac; rewrite (oprod_rec_def ob oc).
move => /funI_P [z /setX_P [za /(oltP ob) zb /(oltP oc) zc] eqa].
set E :=  (osucc a) \times b.
have pz: p (J (Q z) (P z)) by rewrite/p; aw.
move:(proj31_1 zb)(proj31_1 zc)=> or oq. 
have ze: inc (J (Q z) (P z)) E.
  apply: setXp_i; [apply/(oleP oa) | by apply/(oltP ob) ].
  move: (osum_Mle0 (OS_prod2 ob oq) or); rewrite - eqa; apply: oleT.
  apply:(oprod_M1le bp oq).
have pb:singl_val2 (inc^~ E) p. 
   move => u v /setX_P [pu /(oltP osa) oq'' /(oltP ob) or''] vu.
   move => /setX_P [pv /(oltP osa) oq' /(oltP ob) or'] vv.
   move: (proj31_1 or'')(proj31_1 oq'') => r1 r2.
   move: (proj31_1 or')(proj31_1 oq') => r1' r2'.
   have ha: odiv_pr0 a b (P u) (Q u) by [].
   have hb: odiv_pr0 a b (P v) (Q v) by [].
   by move: (odivision_unique oa ob ha hb) => [hc hd]; apply/pair_exten.
move: (select_uniq pb ze pz) => eqb.
by rewrite /odiv_pr1 /oquo/orem -[oquorem a b] eqb; saw.
Qed.

Lemma oquoremP a b: ordinalp a  -> \0o <o b ->
  odiv_pr0 a b (oquo a b) (orem a b).
Proof.
move => oa bp.
have osa :=  (OS_succ oa).
have ob :=  (proj32_1 bp).
have la: a <o (b *o (osucc a)) by apply /oleSltP; apply:oprod_M1le. 
exact:(proj1 (odivision_exists ob osa la)).
Qed.

Lemma oquoremP2 a b q r: ordinalp a  -> \0o <o b ->
  odiv_pr0 a b q r -> q = (oquo a b) /\ r = (orem a b).
Proof.
move => pa pb pc.
move:(oquoremP pa pb) => pd. 
exact (odivision_unique pa (proj32_1 pb) pc pd).
Qed.

End Ordinals1.
Export Ordinals1.
