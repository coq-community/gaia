(** ** Bourbaki  Exercices
 Copyright INRIA (2012-2013 2018) Marelle Team (Jose Grimm). 
*)
(* $Id: ssete5.v,v 1.4 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset15 ssete4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Exercise5.


(** ---- Exercise 5.1:  *)

Lemma Exercise5_1 p n q :
   natp n ->  p <=c n -> q <c p ->
   binom n p = csumb (Nintcc  q (n -c p +c q)) (fun k => 
    binom (n-c (csucc k)) (p -c (csucc q)) *c binom k q).
Proof.
move => nN lepn ltpq.
have pN:= (NS_le_nat lepn nN).
have qN:=(NS_lt_nat ltpq pN).
set E := (Nint n).
set bigset := subsets_with_p_elements p E.
have ce: cardinal E = n by exact: (card_Nint nN).
pose EV X := select (fun x => cardinal (X \cap  (Nint x)) = q) X.
have PA:= (card_p_subsets nN pN ce).
have PB: forall X, inc X bigset ->
  exists ! x, inc x X /\ cardinal (X \cap  (Nint x)) = q.
  move => X /Zo_P [] /setP_P XE cx.
  pose f x := cardinal (X \cap Nint x).
  have f0: f \0c = \0c by  rewrite /f  Nint_co00  setI2_0 cardinal_set0.
  have fn: f n = p by rewrite /f -/E; move /setI2id_Pl: XE => ->.
  have pa: forall x, natp x ->  Nint x +s1 x = Nint (csucc x).
    move => x xn; exact (proj1 (Nint_pr4 xn)).
  have pb: forall x, natp x -> X \cap Nint (csucc x) =
     (X \cap Nint x) \cup (X \cap singleton x).
    by move => x xb; rewrite - set_IU2r - (pa _ xb).
  have fnok: forall x, natp x ->  ~(inc x X) -> f x = f (csucc x).
    move => x xB xX; rewrite /f - (pa _ xB); f_equal.
    set_extens t; move => /setI2_P [sa sb]; apply /setI2_P; split;fprops.
    by case /setU1_P: sb => //  xt; case: xX; rewrite - xt.
  have fok: forall x, natp x -> (inc x X) -> csucc (f x) = f (csucc x).
    move => x xB xX; rewrite /f  (pb _ xB).
    have ->: (X \cap singleton x) = singleton x.
       by apply: set1_pr; fprops => z /setI2_P [_] /set1_P.
    by rewrite csucc_pr //; move /setI2_P => [_] /(NintP xB) [].
  have cax: forall x, cardinalp (f x) by rewrite /f; fprops.
  have fxb x: natp (f x).
     by apply:NS_le_nat pN; rewrite - cx; apply: sub_smaller;apply: subsetI2l.
  have fm: forall x y, natp x -> natp y -> f x <=c f (x +c y).
     move => x y xN yN; move: y yN x xN; apply: Nat_induction.
       move => x xN; rewrite csum0r; fprops.
     move => m mN hrec x xb; move: (hrec _ xb) => pc; apply: (cleT pc).
     rewrite (csum_nS _ mN); case: (inc_or_not (x +c m) X) => h.
     + rewrite - (fok _ (NS_sum xb mN) h); apply:cleS0; fprops.
     + rewrite - (fnok _ (NS_sum xb mN) h); fprops.
  have fm1: forall x y, natp x -> natp y -> x <c y -> inc x X ->
       f x <c f y.
    move => x y xN yN /(cleSltP xN) xy xx; move: (fok _ xN xx) => pc.
    apply /(cleSltP (fxb x)).
    rewrite - (cdiff_pr xy) pc; apply: fm; fprops.
  have XN: sub X Nat by move => t tx; exact: (Nint_S1 (XE _ tx)).
  apply /unique_existence;split; last first.
    move => x y [xx xv][yx yv] ;move: (XN _ xx) (XN _ yx) => xN yN.
    case: (cleT_ell (CS_nat xN)(CS_nat yN)) => // ha.
      by move: (fm1 _ _ xN yN ha xx) => [_]; rewrite /f xv yv.
      by move: (fm1 _ _ yN xN ha yx) => [_]; rewrite /f xv yv.
  have lt1: q <c f n by rewrite fn.
  case: (least_int_prop2 nN lt1 (p := fun k => q <c f k)).
    by rewrite  f0 => /clt0.
  set  x:= cpred _; move =>[xN pe pg].
  exists x; case: (inc_or_not x X) => xx; last first. 
    by case: pg; rewrite (fnok _ xN xx).
  move: pe; rewrite - (fok _ xN xx); move /(cltSleP (fxb x)) => ph.
  split => //; ex_middle eq1; case: pg; split => //; fprops.
have PC: forall X, inc X bigset ->
  ( cardinal (X \cap  (Nint (EV X))) = q /\ inc (EV X) X).
  move => X xb;  move:(PB _ xb) => [z [[za zb] zc]]; apply: select_pr.
      ex_tac.
  by move => a b p1 p2 p3 p4; rewrite - (zc _ (conj p1 p2)) (zc _ (conj p3 p4)).
have PD: forall X, inc X bigset ->  inc (EV X) (Nintcc q (n -c p +c q)).
  move => X px;move: (PC _ px) => [pc pd].
  move: px => /Zo_P [] /setP_P  pa pb.
  have sc: natp ((n -c p) +c q) by fprops.
  move: (Nint_S1 (pa _ pd)) => xN.
  set int := (Nint (EV X)).
  move: (sub_smaller (@subsetI2r X int)); rewrite  pc (card_Nint xN) => pe.
  apply /(Nint_ccP1 qN sc); split => //.
  have pf: sub (X \cap int) (X \cap E).
    by move => T /setI2_P [tx ti]; apply /setI2_P;split => //; apply: pa.
  have pg: cardinal (X \cap E) = p by move /setI2id_Pl: pa => ->.
  have ph: finite_set (X\cap E) by apply/NatP; rewrite  pg.
  move: (pa _ pd) => /(NintP nN) [ltxn _].
  have pf': sub int E by apply:Nint_M1.
  have ph': finite_set E by apply:finite_Nint.
  move: (cardinal_setC4 pf' ph'); rewrite (card_Nint nN) (card_Nint xN).
  move: (cardinal_setC4 pf ph); rewrite pg pc - setIC2 => sa sb.
  move: (sub_smaller (@subsetI2r X (E -s int))); rewrite sa sb.
  rewrite (cdiff_pr8 (proj1 ltpq) lepn nN).
  move => /(cdiff_pr9 (NS_diff q pN) nN xN ltxn); rewrite csumC => ha.
  have hb:= (cleT (cdiff_ab_le_a q (proj31 lepn)) lepn).
  by apply/(cdiff_pr9 xN nN (NS_diff q pN) hb).
transitivity (csumb (Nintcc  q (n -c p +c q)) (fun k => 
     cardinal ( Zo bigset (fun X => EV X = k)))).
  rewrite - PA; apply:card_partition_induced; apply:PD.
apply: csumb_exten => k /Nint_ccP [_  [_ _ lin]].
have ly1: (n -c p +c q) <c n.
  move: (cdiff_pr lepn); set np := (n -c p) => <-.
  rewrite csumC; exact: (csum_Mlteq  (NS_diff _ nN) ltpq).
have ltkn:= cle_ltT lin ly1.
have kN:= (NS_lt_nat ltkn nN).
have sk:= (NS_succ kN).
move / (cleSltP kN): (ltkn) => leskn.
move /(cleSltP qN): (ltpq) => lesqp.
move: (cdiff_pr lesqp); set q':= (p -c csucc q) => eq1.
set I2 := E -s (Nintc k).
have i2p:I2 = E -s Nint (csucc k) by rewrite - (Nint_co_cc kN).
have ci2: cardinal I2 =  (n -c csucc k).
  have pf': sub (Nint (csucc k)) E by apply: Nint_M1.
  have ph': finite_set E by apply: finite_Nint.
  by move: (cardinal_setC4 pf' ph'); rewrite (card_Nint nN) i2p (card_Nint sk).
have q'N: natp q' by rewrite /q'; fprops.
have nskN: natp (n -c csucc k) by  fprops.
move: (card_p_subsets kN qN (card_Nint kN)). 
move: (card_p_subsets nskN q'N ci2).
set Y:= subsets_with_p_elements _ _.
set Z :=  subsets_with_p_elements _ _ => <- <-.
rewrite cprod2cl cprod2cr cprod2_pr1.
symmetry;apply /card_eqP.
pose f z := (P z \cup Q z) +s1 k.
exists (Lf f (Y \times Z) (Zo bigset (fun X => EV X = k))).
have ci2N: natp (cardinal I2) by rewrite ci2; fprops.
have la:lf_axiom f (Y \times Z) (Zo bigset (fun X => EV X = k)).
  move => u /setX_P [pu ] /Zo_P [] /setP_P pa pb /Zo_P [] /setP_P pc pd.
  have pe: sub ((P u \cup Q u) +s1 k) E.
    move => t; case /setU1_P.
       case /setU2_P => ta; first by move /setC_P: (pa _ ta) => [].
       move: (pc _ ta) => /(NintP kN) tk; apply /(NintP nN).
       exact:clt_ltT tk ltkn.
    by move => ->; apply /(NintP nN). 
  have pf: cardinal ((P u \cup Q u) +s1 k) = p.
    have nku: ~ inc k (P u \cup Q u).
      move /setU2_P; case => h.
        move: (pa _ h); rewrite i2p; move=> /setC_P [_]; case.  
        apply/(NintsP kN); fprops.
      by move: (pc _ h)  => /(NintP kN) [_].
    rewrite (csucc_pr nku).
    have di: disjoint (P u) (Q u).
        apply disjoint_pr => t ta tb.
         move: (pa _ ta);  rewrite i2p; move=> /setC_P [_]; case.
       by move: (pc _ tb) =>/ (NintP kN) [le1 _]; apply /(NintsP kN).
    rewrite (csum2_pr5 di) - csum2cr - csum2cl pb pd.
    rewrite - (csum_nS _ qN) cdiff_rpr //.
  have pg: inc (f u) bigset by apply /Zo_P; split => //; apply /setP_P.
  apply /Zo_P; split; first by exact.
  have ph:inc k (f u) /\ cardinal (f u \cap Nint k) = q.
    split; first by apply /setU1_P; right.
    suff: ((P u \cup Q u) +s1 k) \cap Nint k = Q u.
       by rewrite /f => ->.
    set_extens t; last by move => ts; apply /setI2_P; split;fprops.
    move /setI2_P => [sa] /(NintP kN) [tk1 tk2]; case /setU1_P: sa =>//.
     case /setU2_P => // tp; move: (pa _ tp). 
     by rewrite i2p => /setC_P [te] /(NintsP kN).
  have pi:inc (EV (f u)) (f u) /\ cardinal (f u \cap Nint (EV (f u))) = q.
    by  move: (PC _ pg)=> [sa sb].
  move/unique_existence: (PB _ pg) => [_ h]; exact (h _ _ pi ph).
have fi: forall u v, 
  inc u (Y \times Z) -> inc v (Y \times Z) -> f u = f v -> u = v.
  have aux: forall u, inc u  (Y \times Z) ->
    u = J (f u \cap I2) (f u \cap (Nint k)).
     move => u /setX_P [pu ] /Zo_P [] /setP_P pa _ /Zo_P [] /setP_P pb _.
     rewrite - {1} pu /f; congr (J _ _).
     set_extens t.
         move => ts; apply /setI2_P; split;fprops.
       move /setI2_P => [sa]; rewrite i2p => /setC_P [te] /(NintsP kN).
       move => tk;case /setU1_P: sa. 
       by case /setU2_P => // tq; move /(NintP kN): (pb _ tq) => [tk1 _].
       move => tk1; case: tk; rewrite tk1; fprops.
    set_extens t.
        move => ts; apply /setI2_P; split;fprops.
      move /setI2_P => [sa] /(NintP kN) [tk1 tk2]; case /setU1_P: sa =>//.
      case /setU2_P => // tp; move: (pa _ tp). 
      by rewrite i2p => /setC_P [te] /(NintsP kN).
  by move => u v pu pv sv; rewrite (aux _ pu) (aux _ pv) sv.
saw; apply: lf_bijective => //.
move => y /Zo_P [pa pb].
move: (PC _ pa); rewrite pb; move => [pc pd].
set A:=(y \cap Nint k); set B:= (y -s A) -s1 k.
have ay: sub A y by apply subsetI2l.
have Az: inc A Z by apply /Zo_P;split => //; apply /setP_P; apply: subsetI2r.
move: pa => /Zo_P []/setP_P y1 y2.
have b2: sub B I2.
  rewrite i2p;move => t /setC1_P [] /setC_P [ta tb] tc; apply /setC_P.
  split;fprops; move /(NintsP kN) => tk; case: tb; apply /setI2_P.
    split => //;by apply /(NintP kN); split.
have pa: inc k (y -s A). 
  by apply /setC_P;split => //; move /setI2_P => [_] /(NintP kN) [].
move: (cardinal_setC2 ay);rewrite y2 - csum2cl pc  - csum2cr.
rewrite(csucc_pr2 pa) -/B - eq1.
move: (NS_le_nat(sub_smaller b2) ci2N) => cbN.
rewrite  (csum_nS _ cbN) - (csum_Sn _ qN) => h.
move: (csum_eq2l (NS_succ qN) q'N cbN h) => h1.
have By: inc B Y by apply /Zo_P;split => //; apply /setP_P.
exists (J B A); first by apply:setXp_i.
rewrite /f; aw; set_extens t; last first.
    case /setU1_P; last by move => -> ;apply: pd.
    by case /setU2_P; [ move => /setC1_P [] /setC_P [] | move /setI2_P=> []].
move => ty; apply /setU1_P;case: (equal_or_not t k) => tk //; first by right.
left; apply /setU2_P; case: (inc_or_not t A) => ta; first by right.
by left; apply /setC1_P;split => //; apply /setC_P.
Qed.


(** ---- Exercise 5.2 *)

Definition even_card_sub I := Zo (\Po I) (fun z => evenp (cardinal z)).
Definition even_card0_sub I := even_card_sub I -s1 emptyset.
Definition odd_card_sub I := Zo (\Po I) (fun z => oddp (cardinal z)).
Definition Nintc_even p := Zo  (Nintc p) evenp.
Definition Nintc_odd p := Zo  (Nintc p) oddp.


Lemma Exercise5_2 E:
  finite_set E -> nonempty E -> (even_card_sub E) \Eq (odd_card_sub E).
Proof.
move => fse nne.
set n := cardinal E.
pose ce := complement E.
have cs1: forall X, sub (ce X) E by move => X; apply: sub_setC.
have ce2: forall X, sub X E -> cardinal X +c cardinal (ce X) = n.
   by move => x xe; rewrite csum2cr csum2cl - cardinal_setC2.
have fsx: forall X, sub X E -> natp (cardinal X).
   move => x xe;  apply /NatP; apply: (sub_finite_set xe fse).
have cs3: forall X, natp (cardinal (ce X)) by move => X; apply: fsx. 
have cs4: forall X, sub X E -> ce (ce X) = X.
   by  move => X; apply:setC_K.
have nN: natp n by move: fse => /NatP.
case: (p_or_not_p (evenp n)) => ece; last first.
  have oddn: oddp n by split.
  exists (Lf ce (even_card_sub E) (odd_card_sub E)). 
  saw; apply: lf_bijective.
  - move => c /Zo_P [] /setP_P cee evc; apply /Zo_P;split => //. 
      by apply /setP_P.
    split; [by apply: cs3  | move => cxe; case: (proj2 oddn)].
    by move:(csum_of_even evc cxe); rewrite (ce2 _ cee).
  - move => u v  /Zo_P [] /setP_P uE _ /Zo_P [] /setP_P  vE _ /(f_equal ce).
    by rewrite (cs4 _ uE) (cs4 _ vE).
  - move => y =>  /Zo_P [] /setP_P ye yo.
    move: (cs1 y) => xe; rewrite - (cs4 _ ye); exists (ce y)=> //.
    apply: Zo_i; [by apply /setP_P |  ex_middle ceo1].
    by case: ece; rewrite - (ce2 _ ye); apply:(csum_of_odd yo). 
have ce_e: forall X, sub X E -> evenp (cardinal X) -> evenp  (cardinal (ce X)).
  move=> X XE ecx; ex_middle ceo1.
  by move:(proj2 (csum_of_even_odd ecx (conj (cs3 X) ceo1)));rewrite (ce2 _ XE).
move: (rep_i nne); set t:= rep E=> repe.
pose ut x := Yo (inc t x) (x -s1 t) (x +s1 t).
have uut: forall x, sub x E -> (ut (ut x)) = x.
  move => x xE; rewrite /ut; case: (inc_or_not t x) => tx; Ytac0.
    have nst: ~(inc t (x -s1 t)) by move /setC1_P => [].
    by Ytac0; rewrite setC1_K.
  have nst: inc t (x +s1 t) by apply :setU1_1. 
  by Ytac0; apply /setU1_K.
have u1: forall x, sub x E -> sub (ut x) E.
  move => x xe s; rewrite /ut; Ytac st. 
    by move => /setC_P [sx _]; apply: xe.
  by case /setU1_P; [ apply: xe |  move => -> ].
exists (Lf (fun z => ut (ce z)) (even_card_sub E) (odd_card_sub E)). 
saw; apply: lf_bijective.
- move => s => /Zo_P [] /setP_P ta tb; apply /Zo_P; split. 
    apply /setP_P; fprops.
  move: (ce_e _ ta tb) => ec; move:(fsx _ (u1 _ (cs1 s))).
  rewrite /ut; Ytac xt => cb.
    by apply/(succ_of_oddP cb); rewrite - (csucc_pr2 xt).
  by move:(succ_of_even ec); rewrite (csucc_pr xt).
- move => u v  /Zo_P [] /setP_P ue _  /Zo_P [] /setP_P ve _ /(f_equal ut).
  by rewrite (uut _ (cs1 _))  (uut _ (cs1 _)) => /(f_equal ce); rewrite !cs4.
- move => y => /Zo_P [] /setP_P ta tb; move: (u1 _ ta) => ue.
  exists (ce (ut y)) => //; last by rewrite (cs4 _ ue) (uut _ ta).
  apply: Zo_i; [by apply /setP_P |  apply: (ce_e _ ue) ].
  move: (fsx _ ue); rewrite /ut; Ytac xt => cb.
    by apply/(succ_of_evenP cb); rewrite - (csucc_pr2 xt). 
  by move:(succ_of_odd tb); rewrite (csucc_pr xt).
Qed.


Lemma Exercise5_2_alt n: natp n -> n <> \0c ->
  csumb (Nintc_even n) (binom n) = csumb (Nintc_odd n) (binom n).
Proof.
move => nN nz.
set E := Nint n.
have fsE: finite_set E by apply:finite_Nint.
have nE: nonempty E. 
  by exists \0c; apply/NintP; fprops; apply:card_ne0_pos; fprops.
move: (Exercise5_2 fsE nE) => /card_eqP. 
move => h.
have cE: cardinal E = n by apply: card_Nint.
have En: E = n by apply: NintE.
set fe := Lg (Nintc_even n) (fun p => (subsets_with_p_elements p n)).
have ha: forall i, inc i (Nintc_even n) -> cardinal (Vg fe i) = binom n i.
rewrite /fe => i id; rewrite LgV//.
  move/Zo_S:id => /(NintcP nN) lin; move:(NS_le_nat lin nN) => iN.
  by rewrite - (card_p_subsets nN iN cE) En.
have hb: (even_card_sub E)  = unionb fe.
  rewrite /fe  En;set_extens t. 
    move /Zo_P => [/setP_P te ce]; apply/setUb_P.
    have ww: inc (cardinal t) (Nintc_even n). 
      apply /Zo_P; split => //. 
      apply/(NintcP nN); rewrite  - cE; apply:sub_smaller; ue.
    by aw; ex_tac; rewrite LgV//; apply/Zo_P;split => //; apply/setP_P.
  move => /setUb_P; aw; move => [y yi]; rewrite LgV// => /Zo_P [ta tb].
  by apply/Zo_P; split => //; rewrite tb;move: (Zo_hi yi).
have hc:(mutually_disjoint fe).
  apply: mutually_disjoint_prop; rewrite /fe; aw => i j y iA jA; rewrite !LgV//.
  by move=> /Zo_hi <- /Zo_hi <-.
set fo := Lg (Nintc_odd n) (fun p => (subsets_with_p_elements p n)).
have ha': forall i, inc i (Nintc_odd n) -> cardinal (Vg fo i) = binom n i.
  rewrite /fo; aw;move => i id; rewrite LgV//. 
  move/Zo_S:id => /(NintcP nN) lin; move:(NS_le_nat lin nN) => iN.
  by rewrite - (card_p_subsets nN iN cE) En.
have hb': (odd_card_sub E)  = unionb fo.
  rewrite /fo En;set_extens t. 
    move /Zo_P => [/setP_P te ce]; apply/setUb_P.
    have ww: inc (cardinal t) (Nintc_odd n). 
      apply /Zo_P; split => //. 
      apply/(NintcP nN); rewrite  - cE; apply:sub_smaller; ue.
    by aw; ex_tac; rewrite LgV// ; apply/Zo_P;split => //; apply/setP_P.
  move => /setUb_P; aw; move => [y yi]; rewrite LgV// => /Zo_P [ta tb].
  by apply/Zo_P; split => //; rewrite tb;move: (Zo_hi yi).
have hc':(mutually_disjoint fo).
  apply: mutually_disjoint_prop; rewrite /fo; aw => i j y iA jA; rewrite !LgV//.
  by move=> /Zo_hi <- /Zo_hi <-.
transitivity (cardinal (even_card_sub E)).
move: (csum_pr4 hc); rewrite  - hb {1}/fe  => ->.
  by aw; apply:csumb_exten => t ti; symmetry; apply:ha.
move: (csum_pr4 hc'); rewrite h  - hb' {1}/fo  => ->.
by aw; apply:csumb_exten => t ti; apply:ha'.
Qed.

(** -- Exercise 5.3 *)

Definition Exercise5_3V n p k := (binom n k) *c (binom (n -c k) (p -c k)).


Lemma Exercise5_3a E n p k
  (X := Zo (\Po E \times \Po E)
           (fun z => [/\  cardinal (P z) = k,
           cardinal (Q z) = p -c cardinal (P z) & sub (Q z) (E -s P z)])):
  natp n -> natp p -> k <=c p -> cardinal E = n ->
  cardinal X = Exercise5_3V n p k. 
Proof.
move => nN pN lkp ce.
set F1 := subsets_with_p_elements k E.
pose phi := Lf P X F1.
have sp: X = source phi by rewrite /phi; aw.
have tp: F1 = target phi  by rewrite /phi; aw.
have kN: natp k by apply (NS_le_nat lkp pN).
symmetry; rewrite/Exercise5_3V.
rewrite - (card_p_subsets nN kN ce) -/F1 tp sp. 
have lfa: lf_axiom P X F1.
  by move => t /Zo_P [] /setX_P [pa pb pc] [pd _ _]; apply: Zo_i.
have fphi: function phi  by apply: lf_function.
symmetry;apply:(shepherd_principle fphi).
move => x; rewrite - tp => xf.
set K := Vfi1 _ _.
move: (xf) => /Zo_P [] /setP_P xe cx.
have nkN: natp (n -c k) by fprops.
have pkN: natp (p -c k) by fprops.
have fse: finite_set E by apply/NatP; rewrite ce.
have cdx:cardinal (E -s x) = n -c k by rewrite (cardinal_setC4 xe fse) cx ce.
rewrite - (card_p_subsets nkN pkN cdx).
apply /card_eqP.
set K0 := (subsets_with_p_elements (p -c k) (E -s x)).
exists (Lf Q K (subsets_with_p_elements (p -c k) (E -s x))); saw.
have k0p: forall y, inc y K <-> [/\ inc y (\Po E \times \Po E), 
   P y = x & inc (Q y) K0].
  move =>t; apply: (iff_trans  (iim_fun_set1_P x fphi t)).
  rewrite - sp /phi; split.
    move => [tk]; rewrite LfV// => pt.
    move: tk => /Zo_P [te [p1 p2 p3]];split => //; apply/Zo_P. 
    by rewrite -p1;split => //; apply /setP_P; rewrite pt.
   move => [p1 p2 p3]; suff: inc t X by move =>h; rewrite LfV.
   by move/ Zo_P: p3 => [] /setP_P sa sb; apply/ Zo_P; rewrite p2 cx.
apply: lf_bijective.
    by move => t /k0p [_ _].
  move => u v /k0p [u1 pu _]/k0p [v1 pv _] sv.
  by rewrite - (setX_pair u1) - (setX_pair v1) pu pv sv.
move => y yk0; exists (J x y); aw; trivial;apply /k0p; saw.
apply: setXp_i => //; apply /setP_P => //.
by move /Zo_P: yk0 => [] /setP_P h _ t ty; move /setC_P: (h _ ty) => [].
Qed.


Lemma Exercise5_3b n p: natp n -> natp p ->
  csumb (Nintc p) (Exercise5_3V n p)  = \2c  ^c p *c binom n p.
Proof.
move => nN pN.
set E := Nint n.
set F :=subsets_with_p_elements p E.
have ce: cardinal E = n by apply:(card_Nint nN).
set rhs := \2c ^c p *c binom n p.
set EE := (\Po E \times \Po E).
set G1 := Zo EE (fun z => inc (P z) F /\ sub (Q z) (P z)).
have res1: cardinal G1 = rhs.
  pose phi := Lf P G1 F.
  have sp: G1 = source phi by rewrite /phi; aw.
  have tp: F = target phi  by rewrite /phi; aw.
  rewrite /rhs -(card_p_subsets nN pN ce) -/F tp sp cprodC.
  have lfa: lf_axiom P G1 F by move => t /Zo_P [_ []].
  have fphi: function phi by apply: lf_function.
  apply:(shepherd_principle fphi).
  move => x; rewrite - tp => xf.
  set K := Vfi1 _ _.
  pose f := Lf (fun z => J x z) (\Po x) K.
  move /Zo_P: (xf) => [] /setP_P xE cx.
  suff bf: bijection f. 
   by move: (card_bijection bf); rewrite - cx cpowcr - card_setP /f; aw. 
  apply lf_bijective.
  - move => y /setP_P yx. 
    have aux: inc (J x y) G1. 
      apply /Zo_P; saw => //; apply: setXp_i; apply /setP_P => //.
      apply: (sub_trans yx xE).
    apply :(iim_fun_set1_i fphi); rewrite /phi? LfV//; aw; trivial.
  - move => u v _ _ h; exact (pr2_def h).
  - move => y /(iim_fun_set1_P _ fphi) []; rewrite - sp => yG. 
    move /Zo_P: (yG) => [pa [pb pc]]; rewrite /phi LfV// => ->; exists (Q y).
      by apply /setP_P. 
    by rewrite (setX_pair pa).
set G2 := Zo EE (fun z => [/\ cardinal (P z) <=c p,
       cardinal (Q z) = p -c cardinal (P z) & sub (Q z) (E -s  (P z))]).
have fse: finite_set E by apply: finite_Nint.
have res2: cardinal G2 = rhs.
  rewrite - res1; symmetry; apply /card_eqP.
  exists (Lf (fun z => J (Q z) ((P z) -s (Q z))) G1 G2);saw.
  apply: lf_bijective.
  - move => z /Zo_P [] /setX_P [pz Pz Qz] [/Zo_P [_ pc] pb]; apply /Zo_P; aw.
    move /setP_P:Pz => pze; move: (sub_finite_set pze fse) => fsp.
    split; last split.
    + by apply: setXp_i => //; apply /setP_P => t /setC_P [pa _]; apply: pze.
    + by move: (sub_smaller pb); rewrite pc.
    + by rewrite (cardinal_setC4 pb fsp) pc.
    + by move /setP_P:Qz => qze t /setC_P [ta tb]; apply /setC_P;split;fprops.
  - move => u v /Zo_P [pa [_ pb]] /Zo_P [pc [_ pd]] eq1.
    rewrite - (setX_pair pa) - (setX_pair pc) - (setU2_Cr pb) - (setU2_Cr pd).
    by rewrite (pr2_def eq1) (pr1_def eq1).
  - move => y /Zo_P [] /setX_P [pa Py /setP_P Qy] [pb pc pd].
    have a0 : ((P y \cup Q y) -s P y) = Q y.    
      set_extens t; first by  move => /setC_P [] /setU2_P; case.
      move => tq; apply /setC_P; split;fprops => py. 
      by case/setC_P: (pd _ tq).
    have aux: J (P y) ((P y \cup Q y) -s P y) = y by rewrite - [RHS] pa a0.
    have a2:= @subsetU2l  (P y) (Q y).
    move: (Py) => /setP_P Py'.
    have a3:inc (P y \cup Q y) (\Po E)  by apply /setP_P/setU2_12S. 
    have a4:inc (P y \cup Q y) F.
      apply :Zo_i => //; rewrite (cardinal_setC2 a2) a0 - csum2cr - csum2cl.
      by rewrite pc; apply: cdiff_pr.
    exists (J (P y \cup Q y) (P y)); aw; last by rewrite a0 pa.
    by apply /Zo_P; aw;split; [ apply: setXp_i | ].
pose Xk k := Zo EE (fun z => [/\  cardinal (P z) = k,
           cardinal (Q z) = p -c cardinal (P z) & sub (Q z) (E -s P z)]).
set X := Lg (Nintc p) Xk.
have X1: fgraph X by rewrite /X; fprops.
have X2:  mutually_disjoint X. 
  red;rewrite /X; aw => i j ip jp; rewrite !LgV//;mdi_tac nij => u  ua ub; case: nij.
  by move: ua ub => /Zo_hi [<- _ _] /Zo_hi [<- _ _].
have X3: (unionb X) = G2.
   rewrite /X;set_extens t.
     move /setUb_P; aw; move => [y yp]; rewrite LgV//; move /Zo_P => [p1 [p2 p3 p4]].
      by apply /Zo_i => //; rewrite p3 p2; split => //;apply /(NintcP pN).
   move /Zo_P=> [p1 [p2 p3 p4]]; apply /setUb_P;aw.
   by move  /(NintcP pN): p2 => h; ex_tac; rewrite LgV//; apply /Zo_P.
move: (csum_pr4  X2); rewrite X3 res2 => ->.
rewrite /X; aw; symmetry;apply:csumb_exten.
move => k kp; move: (kp) => /(NintcP pN) kp1; rewrite LgV// ;exact:Exercise5_3a.
Qed.

Lemma Exercise5_3c n k p: natp n -> natp p -> k <=c p ->
  Exercise5_3V n p k = (binom p k) *c (binom n p).
Proof.
rewrite /Exercise5_3V => nN pN lkp.
have kN := NS_le_nat lkp pN.
move:(NS_diff k nN) (NS_diff k pN) => nkN pkN.
case: (NleT_el pN nN) => lpn; last first.
  rewrite (binom_bad nN pN lpn) cprod0r.
  case: (NleT_el kN nN) => lkn.
    have l2: (n -c k) <c (p -c k) by apply (cdiff_pr7 lkn lpn pN).
    by rewrite (binom_bad nkN pkN l2) cprod0r.
  by rewrite (binom_bad nN kN lkn) cprod0l.
have lkn:= cleT lkp lpn.
have l3: (p -c k) <=c (n -c k).
  case: (equal_or_not p n) => epn; first by rewrite epn; fprops.
  exact: (proj1 (cdiff_pr7 lkp (conj lpn epn) nN)).
have npN := NS_diff p nN.
have ha:=(binom_good nN kN lkn).
have hb:=(binom_good nkN pkN l3).
have hc:=(binom_good pN kN lkp).
have hd:=(binom_good nN pN lpn).
have x1N: natp (binom n k *c binom (n -c k) (p -c k)). 
  by apply:NS_prod; apply:NS_binom.
have x2N: natp (binom p k *c binom n p)  by apply:NS_prod; apply:NS_binom.
have x3N: natp ((factorial k) *c factorial (n -c k)).  
  by apply:NS_prod; apply:NS_factorial.
have x3z: ((factorial k) *c factorial (n -c k)) <> \0c.
  by apply: cprod2_nz; apply: factorial_nz.
have x4N: natp (binom (n -c k) (p -c k) *c factorial n). 
  by apply:NS_prod; [ apply: NS_binom | apply:NS_factorial].
have fpkN:=(NS_factorial pkN).
have x5N:natp (binom n p *c (factorial p *c factorial (n -c k))).
  by apply:NS_prod; [ apply:NS_binom | apply: NS_prod; apply:NS_factorial].
have sa:((n -c k) -c (p -c k)) = n -c p.
  by have d1:= (cdiff_pr lkp); rewrite (cdiffA nN kN pkN) d1.
rewrite sa in hb.
apply: (cprod_eq2r x3N x1N x2N x3z).
rewrite (cprodC (binom n k)) - cprodA ha. 
apply:(cprod_eq2r fpkN x4N (NS_prod x2N x3N) (factorial_nz pkN)).
rewrite (cprodC (binom p k)) cprodA -3!(cprodA (binom n p)).
set x := (binom p k *c factorial k). 
rewrite - (cprodA x) (cprodC (factorial (n -c k)))  (cprodA x) /x.
rewrite - (cprodA  (binom p k)) hc.
apply:(cprod_eq2r (NS_factorial npN) (NS_prod x4N fpkN) x5N (factorial_nz npN)).
set y:=(factorial n); rewrite (cprodC _ y) -(cprodA y) - {1} (cprodA y).
rewrite - (cprodA (binom _ _))  hb cprodA - cprodA.
by rewrite  (cprodC (factorial (n -c k))) cprodA - (cprodA (binom n p)) hd.
Qed.

Lemma Exercise5_3d n p: natp n -> natp p ->
  csumb (Nintc p) (Exercise5_3V n p) = \2c ^c p *c binom n p.
Proof.
move => nN pN.
transitivity (csumb (Nintc p) (fun k => (binom n p) *c (binom p k) )).
  apply: csumb_exten => k /(NintcP pN) lmn. 
  by rewrite [in RHS] cprodC; apply:Exercise5_3c.
by rewrite - (sum_of_binomial pN) cprodC cprod2Dn (NintcE pN).
Qed.


Lemma Exercise5_3e n p: natp n -> natp p -> p <> \0c ->
    csumb (Nintc_even p) (Exercise5_3V n p)  
  = csumb (Nintc_odd p) (Exercise5_3V n p). 
Proof.
move => nN pN pnz.
set A:= (Nintc_even p); set B:= (Nintc_odd p). 
transitivity (csumb A (fun k => (binom n p) *c (binom p k) )).
  apply: csumb_exten => k /Zo_S /(NintcP pN) lmn. 
  by rewrite [in RHS] cprodC; apply:Exercise5_3c.
transitivity (csumb B (fun k => (binom n p) *c (binom p k))); last first.
  apply: csumb_exten => k /Zo_S /(NintcP pN) lmn; symmetry.
  by rewrite [in RHS] cprodC; apply:Exercise5_3c.
by rewrite - cprod2Dn - cprod2Dn  Exercise5_2_alt.
Qed.
  
(**  exercise 5.4 is in the main text *)



(** -- exercise 5.5 *)

Lemma odd_zero: ~ (oddp \0c).
Proof. case => _; case; exact: even_zero. Qed.

Lemma odd_nonempty x:  oddp (cardinal x) -> nonempty x.
Proof.
move => h; apply /nonemptyP => h1.
move: h; rewrite h1 cardinal_set0; apply: odd_zero.
Qed.


Section Exercise5_5.
Variables (E r: Set) (f: Set -> Set).
Hypothesis lr:lattice r.
Hypothesis dl: distributive_lattice1 r.
Hypothesis sr: E = substrate r.
Hypothesis card_f: forall x, inc x E -> cardinalp (f x).
Hypothesis hyp_f: forall x y, inc x E -> inc y E ->
    (f x) +c (f y) = (f (sup r x y)) +c f (inf r x y).


Definition  Exercise5_5_conc I :=
   f (supremum r I) +c 
       csumb (even_card0_sub I) (fun z => f (infimum r z))
    = csumb (odd_card_sub I) (fun z => f (infimum r z)).
Definition  Exercise5_5_conc_aux I g :=
  f (supremum r (fun_image I g)) +c 
       csumb (even_card0_sub I) (fun z => f (infimum r (fun_image z g)))
    = csumb  (odd_card_sub I) (fun z => f (infimum r (fun_image z g))).

Lemma Exercise5_5_a1 n g (I:=Nintc n):
   natp n -> (forall i, inc i I -> inc (g i) E) ->
   Exercise5_5_conc_aux I g.
Proof.
move => nN;rewrite /I; clear I; move: n nN g.
move: (proj1 lr) => or.
apply: Nat_induction.
   rewrite Nint_cc00 /Exercise5_5_conc_aux; move =>g H. 
   rewrite /csumb; set f1 := Lg _ _; set f2 := Lg _ _.
   have pA: domain f1 = emptyset.
      rewrite /f1; aw; apply /set0_P => s /Zo_P [] /Zo_P [].
      rewrite setP_1; case /set2_P => ->; first by move => _ /set1_P.
      by rewrite cardinal_set1; move: odd_one => [].
   have pE: inc (g \0c) (substrate r) by rewrite - sr; apply: H; fprops.
   have pB: inc (singleton \0c) (odd_card_sub (singleton \0c)).
     apply /Zo_P; split; first by apply /setP_P; fprops. 
     rewrite cardinal_set1; apply: odd_one.
   have pC: domain f2 = singleton (singleton \0c).
     rewrite /f2; aw; apply: set1_pr => //.
     move => z /Zo_P [];rewrite setP_1; case /set2_P => -> //.
     by rewrite cardinal_set0 => /odd_zero.
   have pG: cardinalp (f (g \0c)) by apply:card_f; apply: H; fprops.
   rewrite (csum_trivial1 pC) /f2 LgV// funI_set1 (csum_trivial pA). 
   rewrite (supremum_singleton or pE)(infimum_singleton or pE) card_card // csum0r//.
move => n nN Hrec g gse.
move: (NS_succ nN) => snN.
set I1 := (Nintc (csucc n)).
set I := (Nintc n); set z := csucc n.
have [pa pb]: I +s1 z = I1 /\  ~ inc z I.
  rewrite /I /I1 (Nint_co_cc nN) (Nint_co_cc snN); apply: (Nint_pr4 snN).
rewrite / Exercise5_5_conc_aux - {1} pa funI_setU1.
have gxsr: forall i, inc i I1 -> inc (g i) (substrate r) by ue. 
have gzr: inc (g z) (substrate r) by apply: gxsr; apply/NintcP; fprops.
have sii': sub I I1 by rewrite -pa => t ti; fprops.
have fsI1: finite_set I1 by apply /NatP; rewrite card_Nintc; fprops.
have fsI: finite_set I by apply /NatP; rewrite card_Nintc.
pose g' x := inf r (g x) (g z).
have g'xsr: forall x, inc x I1 -> inc (g' x) (substrate r).
   move: (lattice_props lr) => [p1 [p2 _]]. 
   by move => x xI; apply: (p2 _ _ (gxsr _ xI) gzr).
have sr1: forall s, sub s I1 -> sub (fun_image s g) (substrate r).
  by move => s si t /funI_P [u us ->];apply: gxsr; apply: si.
have sr1': forall s, sub s I1 -> sub (fun_image s g') (substrate r).
  by move => s si t /funI_P [u us ->]; apply: g'xsr; apply: si.
have fs1: forall s, sub s I1 -> finite_set (fun_image s g).
   move => s si;  apply: finite_fun_image; apply: (sub_finite_set si fsI1).
have fs1': forall s, sub s I1 -> finite_set (fun_image s g').
  move => s si;  apply: finite_fun_image; apply: (sub_finite_set si fsI1).
have rec1: 
   (inf r (supremum r (fun_image I g)) (g z)) = supremum r (fun_image I g').
  have h := (proj1 (distributive_lattice_prop1 lr)).
  have h1:= (proj33 (distributive_lattice_prop2 lr)). 
  move: (h1 (h dl)) => dl2; clear h h1.
  have dl2': forall a b, inc a E -> inc b E ->
    inf r (sup r a b) (g z) = sup r (inf r a (g z)) (inf r b (g z)).
    by rewrite sr;move => a b ae be; rewrite inf_C dl2 // inf_C (inf_C r b).
  suff: forall m, natp m -> m <=c n -> 
      inf r (supremum r (fun_image (Nintc m) g)) (g z) =
        supremum r (fun_image (Nintc m) g').
      move => aux; apply: (aux n nN); fprops.
  apply: Nat_induction.
    move => h; rewrite Nint_cc00 (funI_set1 g \0c) (funI_set1 g' \0c).
    have oi: inc \0c I1 by apply:sii';apply /(NintcP nN).
    have aa: inc (g \0c) (substrate r) by apply: gxsr.
    by rewrite supremum_singleton //supremum_singleton //; apply: g'xsr.
  move => m mN Hrec1 smn; move: (NS_succ mN) => smN.
  move: (proj1 (Nint_pr4 smN)).
  have sim: inc (csucc m) I1 by apply: sii';apply /(NintcP nN).
  move: (cleS mN) => lemsm; move: (cleT lemsm smn) => le3.
  rewrite - (Nint_co_cc mN) - (Nint_co_cc smN); move => <-.
  have smI: sub (Nintc m) I1.
     move => t  /(NintcP mN)=> tb; apply: sii'; apply /(NintcP nN). 
     by apply: (cleT tb le3).
  move: (sr1 _ smI)  (sr1' _ smI)(fs1 _ smI)  (fs1' _ smI)  => sa sa' sc sc'.
  have sb: nonempty (fun_image (Nintc m) g).
     exists (g m); apply /funI_P; exists m => //; apply /NintcP; fprops.
  have sb': nonempty (fun_image (Nintc m) g').
     exists (g' m); apply /funI_P; exists m=> //; apply /NintcP; fprops.
  have sd: inc (g (csucc m)) (substrate r) by apply: gxsr. 
  have sd': inc (g' (csucc m)) (substrate r) by apply: g'xsr.
  have se: inc (supremum r (fun_image (Nintc m) g)) (substrate r).
    by apply: (inc_supremum_substrate or sa); apply: lattice_finite_sup2.
  rewrite 2!funI_setU1 sup_setU1 // sup_setU1 // - (Hrec1 le3).
  by rewrite inf_C dl2 // inf_C (inf_C _ (g z)) -/(g' (csucc m)).
have inf_gp: forall s, sub s I -> nonempty s ->
  infimum r (fun_image (s +s1 z) g) = (infimum r (fun_image s g')).
  move => s sa sb.
  have fs: finite_set s by  apply: (sub_finite_set sa fsI).
  pose b s := infimum r (fun_image (s +s1 z) g) = infimum r (fun_image s g').
  pose a s := sub s I.
  have p1: forall u, a (singleton u) -> b (singleton u).
     move =>  u h; rewrite /b funI_setU1 2! funI_set1.
     have  ui: inc u I1 by  apply: sii';apply:h; fprops.
     rewrite (infimum_singleton or (g'xsr _ ui)) setU2_11 //.
  apply:(finite_set_induction2 p1 _ fs) => //.
  move => u v h neu; rewrite /a /b => ra.
  have vi1: inc v I1 by apply: sii'; apply: ra; fprops.
  have gvr: inc (g v) (substrate r) by apply (gxsr _ vi1).
  have gvr': inc (g' v) (substrate r) by apply (g'xsr _ vi1).
  have ->:  ((u +s1 v) +s1 z) = (((u +s1 z) +s1 v) +s1 z).
    rewrite - 3!setU2_A  (setU2_C _ (singleton z)).
    by rewrite (setU2_A (singleton z)) setU2_id.
  have au: a u by move => t tu;apply: ra; fprops.
  have ne1: nonempty (fun_image ((u +s1 z) +s1 v) g).
      exists (g v); apply: funI_i; fprops.
  have ne2: nonempty (fun_image (u +s1 z) g).
     exists (g z); apply: funI_i; fprops.
  have ne3: nonempty (fun_image u g').
    move:neu => [t tu]; exists (g' t); apply: funI_i; fprops.
  have aux1: sub ((u +s1 z) +s1 v) I1.
     move => t; case /setU1_P; last by move => ->.
     case /setU1_P; first by move => tu;apply: sii'; apply: au.
     move => ->; apply /(NintcP snN); fprops.
  have aux2: sub (u +s1 z) I1 by move => t ts; apply: aux1; apply/setU1_P; left.
  have aux3: sub u I1 by move => t ts; apply: sii'; apply: au.
  have aux4:inc (infimum r (fun_image (u +s1 z) g)) (substrate r).
    apply: (inc_infimum_substrate or (sr1 _ aux2)).
    apply: (lattice_finite_inf2 lr  (fs1  _ aux2) ne2 (sr1 _ aux2)).
  rewrite funI_setU1 (inf_setU1 lr (sr1 _ aux1) ne1 (fs1  _ aux1) gzr).
  rewrite funI_setU1 (inf_setU1 lr (sr1 _ aux2) ne2 (fs1  _ aux2) gvr).
  move: (lattice_props lr) => [_ [ _ [_ [_ [_ [idr _]]]]]].
  rewrite - (idr _ _ _ aux4 gvr gzr) -/(g' v) [in RHS] funI_setU1.
  by rewrite (inf_setU1 lr (sr1' _ aux3) ne3 (fs1' _ aux3) gvr') (h neu au).
have gIr: sub  (fun_image I g) (substrate r) by apply: sr1.
have gIhs: has_supremum r (fun_image I g).
   apply: lattice_finite_sup2 => //; first by apply: finite_fun_image. 
   exists (g n); apply : funI_i; apply/NintcP; fprops.
move : (inc_supremum_substrate or gIr gIhs); rewrite - sr => sIE.
have pc: forall i, inc i I -> inc (g i) E.
   by rewrite sr => i iI; apply:gxsr; apply: sii'.
have pd: forall i, inc i I -> inc (g' i) E.
   by rewrite sr => i iI; apply:g'xsr; apply: sii'.
move: (Hrec _ pc) (Hrec _ pd);rewrite / Exercise5_5_conc_aux.
set seG := csumb _ _;set soG := csumb _ _.
set seG' := csumb _ _;set soG' := csumb _ _.
set seI := csumb _ _; set soI := csumb _ _.
set X := f _; set X':= f _; set X'' := f _ => r1 r2.
move: (gzr); rewrite - sr => gzE.
move: (hyp_f sIE gzE); rewrite rec1 - (supremum_setU1 lr gIr gIhs gzr) => auxx.
clear gIr gIhs sIE pc pd gzE.
have ->: seI = seG +c soG'.
  set A := even_card0_sub I.
  set B := fun_image (odd_card_sub I) (fun t => t +s1 z).
  have dAB: disjoint A B.
     apply: disjoint_pr => u /Zo_P [] /Zo_P [] /setP_P ra rb rc /funI_P.
     move => [t _ h]; case: pb; apply: ra; rewrite h; fprops.
  have uAB: (even_card0_sub I1) = A \cup B.
     rewrite /B;set_extens t.
       move => /Zo_P [] /Zo_P [] /setP_P ra rb te; apply /setU2_P.
       case: (inc_or_not z t) => zt.
         right; apply /funI_P; exists (t -s1 z);last by rewrite (setC1_K zt).
         apply /Zo_P; split. 
           apply /setP_P => s /setC1_P [st sz];move: (ra _ st); rewrite -pa.
           by case /setU1_P.
         move: (csucc_pr2 zt) => e1.
         split; first by apply:NS_nsucc; fprops;rewrite -e1; exact (proj1 rb).
         by move /succ_of_even; rewrite- (csucc_pr2 zt); case.
       left; apply /Zo_P;split => //; apply /Zo_P;split => //; apply /setP_P.
       move => s st;move: (ra _ st); rewrite -pa;case /setU1_P => //.
       by move => sz; case: zt; rewrite - sz.
    case /setU2_P.
      move => /Zo_P [] /Zo_P [] /setP_P ra rb rc; apply/Zo_P;split => //.
      apply /Zo_P;split => //; apply /setP_P; rewrite -pa => s st. 
      by apply /setU1_P; left; apply: ra.
    move /funI_P => [s ] /Zo_P [] /setP_P sa sb ->; apply/ Zo_P.
    split; last by apply /set1_P;apply /nonemptyP; exists z; fprops.
    apply /Zo_P; split; first by apply /setP_P; rewrite -pa; apply:setU2_S2. 
    have zs: ~ inc z s by move => h; case: pb; apply: sa.
    rewrite (csucc_pr zs); apply: (succ_of_odd sb).
  move: (csumA_setU2 (fun z => f (infimum r (fun_image z g))) dAB).
  suff: csumb B (fun s => f (infimum r (fun_image s g))) = soG'.
      by move => ->; rewrite - uAB.
  have qx:quasi_bij (fun t => t +s1 z) (odd_card_sub I) B.
    split; [ by move => s sa; apply: funI_i | |  by move => y /funI_P].
    move => u v /Zo_P [] /setP_P ui _ /Zo_P [] /setP_P vi _ sv.
    have nzu: ~ (inc z u) by move => b; apply: pb; apply: ui.
    have nzv: ~ (inc z v) by move => b; apply: pb; apply: vi.
    by rewrite  - (setU1_K nzu) sv (setU1_K nzv).
  rewrite (csum_Cn2 _ qx); apply:csumb_exten => s /Zo_P [/setP_P sb sc].
  by rewrite inf_gp //; apply:odd_nonempty.
have ->: soI = soG +c seG' +c (f (g z)).
  rewrite /soI /soG /seG' -/I.
  set A := odd_card_sub I; 
  set B := fun_image (even_card_sub I) (fun t => t +s1 z).
  have dAB: disjoint A B.
     apply: disjoint_pr => u /Zo_P [] /setP_P ra rb  /funI_P.
     move => [t _ h]; case: pb; apply: ra; rewrite h; fprops.
  have uAB: (odd_card_sub I1) = A \cup B.
    set_extens t.
      move => /Zo_P []/setP_P ra rb; apply /setU2_P.
      case: (inc_or_not z t) => zt.
        right;apply /funI_P; exists (t -s1 z); last by rewrite (setC1_K zt).
        apply /Zo_P; split.
          apply /setP_P => s /setC1_P [st sz];move: (ra _ st); rewrite -pa.
          by case /setU1_P.
        move: (csucc_pr2 zt) => e1; ex_middle bad.
        have oi: oddp (cardinal (t -s1 z)).
          split => //; apply:NS_nsucc; fprops;rewrite -e1; exact (proj1 rb).
        by move: (succ_of_odd oi); rewrite - e1 => h; case: rb.
        left; apply /Zo_P;split => //; apply /setP_P.
      move => s st;move: (ra _ st); rewrite -pa;case /setU1_P => //.
      by move => sz; case: zt; rewrite - sz.
    case /setU2_P.
      move => /Zo_P [] /setP_P ra rb; apply/Zo_P;split => //; apply /setP_P.
      apply: (sub_trans ra sii').
    move /funI_P => [s] /Zo_P [] /setP_P sa sb ->; apply/ Zo_P.
    split;first by apply /setP_P; rewrite -pa; apply:setU2_S2.
    have zs: ~ inc z s by move => h; case: pb; apply: sa.
    rewrite (csucc_pr zs); apply: (succ_of_even sb).
  move: (csumA_setU2 (fun z => f (infimum r (fun_image z g))) dAB).
  rewrite uAB => ->; rewrite - csumA; congr (_ +c _).
  rewrite /B.
  have ->: even_card_sub I = even_card0_sub I +s1 emptyset.
    set_extens t. 
       move => h; apply/setU1_P;case: (emptyset_dichot t) => sd; first by right.
       by left; apply /Zo_P; split => //; move /set1_P; apply /nonemptyP.
    case /setU1_P; [ by move /Zo_P => [] | move => ->; apply /Zo_P].
    split; first by apply: setP_0i.
    by rewrite cardinal_set0; apply: even_zero.
  have di2: disjoint (fun_image (even_card0_sub I) (fun t => t +s1 z))
     (singleton (singleton z)).
     apply: disjoint_pr => u /funI_P [v] /Zo_P [] /Zo_P [sa sb].
     move /set1_P => vne eq1 /set1_P uz; move: sb.
     have ->: v = singleton z.
        apply : set1_pr1; first by apply /nonemptyP.
        move => t tv; apply /set1_P; rewrite -uz  eq1; fprops.
    rewrite cardinal_set1; exact (proj2 odd_one).
  rewrite funI_setU1 set0_U2 (csumA_setU2 _ di2).
  rewrite {2} /csumb; set f2 := Lg _ _.
  have sid: domain f2 = (singleton (singleton z)) by rewrite /f2; aw.
  have ww: inc (singleton z) (singleton (singleton z)) by fprops.
  have eq1: Vg f2 (singleton z) = f (g z).
      rewrite /f2 LgV// funI_set1 // infimum_singleton //. 
  have cf1: cardinalp (f (g z)) by apply: card_f; ue.
  rewrite (csum_trivial1 sid) eq1 (card_card cf1)  csumC (csumC _ (f (g z))). 
  apply:f_equal.
  set B1:= fun_image _ _.
  have qx:quasi_bij (fun t => t +s1 z) (even_card0_sub I) B1.
    split; [ by move => s sa; apply: funI_i | | by move => y /funI_P].
    move => u v /Zo_P [] /Zo_P [] /setP_P ui _ _. 
    move => /Zo_P []  /Zo_P [] /setP_P vi _ _ sv.
    have nzu: ~ (inc z u) by move => b; apply: pb; apply: ui.
    have nzv: ~ (inc z v) by move => b; apply: pb; apply: vi.
    by rewrite - (setU1_K nzu) sv (setU1_K nzv).
  rewrite (csum_Cn2 _ qx); apply: csumb_exten => s sa.
  move /Zo_P: (sa) => [] /Zo_P [] /setP_P sb sc /set1_P /nonemptyP sd.
  by rewrite inf_gp //. 
rewrite -r2 -r1  (csumA seG) (csumC seG) 2!csumA  -auxx -/X - (csumA X).
by rewrite (csumC (f (g z))) csumA - csumA (csumC (f (g z))) {1} csumA.
Qed.

Lemma Exercise5_5_a2 I: sub I E -> nonempty I -> finite_set I ->
   Exercise5_5_conc I.
Proof.
move => IE neI fsi.
set m := cardinal I.
have mN: natp m by  apply /NatP.
have mz: m <> \0c by move:(card_nonempty1 neI).  
move: (card_Nintcp mN mz); move /card_eqP.
move: (cpred_pr mN mz) => [pa pb].
move => [G [bG sG tG]].
have fg: function G by fct_tac.
set K := Nintc (cpred m).
pose g x := Vf G x.
have aux: forall x, inc x K -> inc (g x) E.
  rewrite /K - sG; move => x xk; apply: IE; rewrite - tG /g; Wtac.
move: (Exercise5_5_a1 pa aux). 
rewrite /Exercise5_5_conc_aux /Exercise5_5_conc.
have ->:(fun_image (Nintc (cpred m)) g) = I.
  rewrite - sG - tG;set_extens t. 
     move /funI_P; rewrite /g; move => [z za ->]; Wtac.
   move => tg; move: (bij_surj bG tg) => [x xs ->]. 
   apply /funI_P; ex_tac.
have ga: forall t, sub t  (source G) -> sub (fun_image t g) I.
   move => t tg s /funI_P [z zt ->]; rewrite -tG /g; Wtac.
have gb: forall t, sub t  (source G) ->
   cardinal t = cardinal (fun_image t g).
   move => t tg; symmetry; apply cardinal_fun_image.
   move => u v ut vt sg; move: (tg _ ut) (tg _ vt) => ug vg.
   apply: (bij_inj bG ug vg sg).
have gc: forall u v, sub u (source G) -> sub v (source G) ->
   fun_image u g = fun_image v g -> u = v.
   move => u v us vs sf; set_extens t => tu.
     have : inc (g t) (fun_image v g) by rewrite - sf; apply: funI_i.
     move /funI_P => [z za zb].
     by rewrite (bij_inj bG  (us _ tu)(vs _ za) zb).
   have : inc (g t) (fun_image u g) by rewrite  sf; apply: funI_i.
   move /funI_P => [z za zb].
   by rewrite  (bij_inj bG (vs _ tu) (us _ za)  zb).
have gd: forall u, sub u I -> exists2 t, sub t (source G)& (fun_image t g) =u.
   move => u uI; exists (Zo (source G) (fun z => inc (g z) u)).
      by apply: Zo_S.
   set_extens t; first by move => /funI_P [z ] /Zo_P [] _ h ->.
   rewrite -tG in uI; move => tu; move: (bij_surj bG (uI _ tu)) => [x p1 p2].
   apply /funI_P; rewrite p2 /g; exists x => //; apply: Zo_i => //; ue.
have ra: quasi_bij(fun_image^~ g)(even_card0_sub (source G)) (even_card0_sub I).
 split.
  + move => t /Zo_P [] /Zo_P [] /setP_P  t1 t2 /set1_P te.
    apply /Zo_P; split.
      apply /Zo_P; split; first by apply /setP_P; fprops.
      by rewrite - (gb _ t1).
    apply /set1_P => e; case: (emptyset_dichot t) => //; move => [s st].
    by empty_tac1 (g s); apply: funI_i.
 + move => u v /Zo_P [] /Zo_P [] /setP_P h1 _ _. 
   by move => /Zo_P [] /Zo_P [] /setP_P h2 _ _; apply: gc.
 + move => y /Zo_P [] /Zo_P [] /setP_P p1 p2 p3.
   move: (gd _ p1) => [t t1 t2]; exists t => //; apply /Zo_P; split. 
     apply /Zo_P; split; first by apply/setP_P. 
     by rewrite (gb _ t1) t2.
   move /set1_P => h1; case: p3; apply /set1_P; rewrite -t2.
   by rewrite h1; apply /set0_P => s /funI_P [z] /in_set0.
rewrite - sG  (csum_Cn2 _ ra) => ->.
symmetry;apply: csum_Cn2; split.
+ move => t /Zo_P [] /setP_P p1 p2; apply /Zo_P;rewrite - (gb _ p1);split=> //.
 apply /setP_P; fprops.
+ by move => u v /Zo_P [] /setP_P us _  /Zo_P [] /setP_P vs _; apply: gc.
+ move => y /Zo_P [] /setP_P p1 p2; move: (gd _ p1) => [t t1 t2].
  exists t => //; apply /Zo_P; split; first by apply /setP_P.
  by rewrite (gb _ t1) t2.
Qed.

End  Exercise5_5.

Lemma setP_lattice_d1 A: distributive_lattice1 (subp_order A).
Proof.
rewrite /distributive_lattice1 (proj2 (subp_osr A)) => x y z xA yA zA.
rewrite (proj1 (setP_lattice_pr xA yA))  (proj1 (setP_lattice_pr xA zA)).
rewrite (proj2 (setP_lattice_pr yA zA)).
move: (xA)(yA)(zA) => /setP_P xA' /setP_P yA' /setP_P zA'. 
have yzA: inc (y \cap z) (\Po A) by apply/setP_P/subI2_set; left.
have xyA: inc (x \cup y) (\Po A) by apply/setP_P/setU2_12S.
have xzA: inc (x \cup z) (\Po A) by apply/setP_P/setU2_12S.
rewrite (proj1 (setP_lattice_pr xA yzA)) (proj2 (setP_lattice_pr xyA xzA)).
by rewrite  set_UI2r.
Qed.

Lemma Exercise5_5_b1 x y: 
  cardinal x +c cardinal y = cardinal (x \cup y) +c cardinal (x \cap y).
Proof.
have di: disjoint (x -s y) (x \cap y).
  by apply: disjoint_pr => u /setC_P [_ pa] /setI2_P [].
move: (csum2_pr5(set_I2Cr x y)); rewrite setU2Cr2 setU2_C => ->.
rewrite csum2cr csum2cr - csumA - (csum2_pr5 di).
by rewrite - setCC_r setC_v setC_0 csumC.
Qed.


Lemma Exercise5_5_b3 I (f: fterm) : finite_set I ->
  cardinal (unionf I f) +c 
       csumb (even_card0_sub I) (fun z => cardinal (intersectionf z f))
    = csumb (odd_card_sub I) (fun z => cardinal (intersectionf z f)).
Proof.
case: (emptyset_dichot I).
  move => ->; rewrite setUf_0 cardinal_set0.
  have ->: (even_card0_sub emptyset) = emptyset.
    by apply /set0_P => t /setC1_P [] /Zo_S /setP_P /sub_set0 h. 
  have ->: (odd_card_sub emptyset) = emptyset.
    apply /set0_P => t /Zo_P [] /setP_P/sub_set0 ->.
    by rewrite cardinal_set0 => /odd_zero.
  rewrite csum0l //; apply:CS_cardinal.
move => neI fse.
set m := cardinal I.
have mN: natp m by apply/NatP.
have mz: m <> \0c by apply:card_nonempty1.
move:(card_Nintcp mN mz); move /card_eqP.
move: (cpred_pr mN mz); set n := cpred m; move=> [pa pb] [G [bG sG tG]].
have fg: function G by fct_tac.
pose g i := f (Vf G i).
set A := unionf I f; set E := \Po A;set r:= subp_order A.
have esr: E = substrate r by symmetry; apply: (proj2 (subp_osr A)).
have lr: lattice r by apply: setP_lattice.
move: (@setP_lattice_d1 A) => dl1.
have cf: forall x, inc x E -> cardinalp (cardinal x) by move => x _; fprops.
have fp: forall x y, inc x E -> inc y E -> 
     cardinal x +c cardinal y = cardinal (sup r x y) +c cardinal (inf r x y).
  move => x y xe ye; move: (setP_lattice_pr xe ye) => [-> ->].
  apply: Exercise5_5_b1.
have pc: (forall i, inc i (Nintc n) -> inc (g i) E).
  rewrite - sG => i iG; move: (Vf_target fg iG); rewrite tG => h.
  apply /setP_P => s sa; apply /setUf_P; ex_tac.
move: (Exercise5_5_a1 lr dl1 esr cf fp pa pc). 
rewrite /Exercise5_5_conc_aux.
set J := (Nintc n).
have pd: sub (fun_image J g) (\Po A).
   by move => t /funI_P [z za zb]; move: (pc _ za); rewrite zb.
move: (setU_sup pd) => h; rewrite - (supremum_pr2 (proj1 lr) h).
have pe: forall x, sub x J -> (fun_image x g) = fun_image (Vfs G x) f.
   rewrite /J - sG; move => x xJ.
    set_extens t => /funI_P [z za ->]; apply /funI_P.
      exists (Vf G z) => //; apply/ (Vf_image_P fg xJ); ex_tac.
    move /(Vf_image_P fg xJ): za => [u ux ->]; ex_tac.
have ->: (fun_image J g) = fun_image I f.
  by rewrite -tG - (surjective_pr0 (proj2 bG)) /Imf sG; apply: pe.
have ->: union (fun_image I f) = A.
  set_extens t. 
     move /setU_P => [z tz] /funI_P [u ui uv]; apply /setUf_P; ex_tac; ue.
  by move/setUf_P => [y yi tf]; apply /setU_P; exists (f y) => //; apply:funI_i.
have pf: forall x, inc x (\Po J) -> nonempty x -> 
  (infimum r (fun_image x g)) = intersectionf  (Vfs G x) f.
  move => x /setP_P qa qb. 
  have ta: nonempty (fun_image x g) by apply: funI_setne.
  have tb: sub (fun_image x g) (\Po A).
     by move => t /funI_P [z zx ->]; apply: pc; apply: qa.
  move: (ta); rewrite {1} (pe _ qa) => ta1.
  have tc: nonempty (Vfs G x). 
    by apply /nonemptyP => ba; move: ta1; rewrite ba funI_set0 => /nonemptyP.
  move: (setI_inf tb); Ytac0 => h1; rewrite - (infimum_pr2 (proj1 lr) h1).
  rewrite (pe _ qa); set_extens t.
     move /(setI_P ta1) => hi; apply: (setIf_i tc) => j ja.
     by apply: hi; apply: funI_i.
  move /(setIf_P _ tc) => hi;apply: (setI_i ta1) => j /funI_P [z za ->].
  by apply: hi.
have pg: forall s, sub s J -> sub (Vfs  G s) I.
   by rewrite -tG; move => s sj; apply: fun_image_Starget1.
have ph: forall s, sub s J -> cardinal (Vfs G s) = cardinal s.
  move => s sj; symmetry;apply /card_eqP.
  apply Eq_restriction1;[ ue | exact (proj1 bG)].
have pi: forall u v, sub u J -> sub v J ->
    Vfs G u = Vfs G v -> u = v.
  rewrite /J - sG;  move => u v uJ vJ si; set_extens t => tu.
     have : inc (Vf G t) (Vfs G v).
       rewrite - si; apply /(Vf_image_P fg uJ); ex_tac.
     move /(Vf_image_P fg vJ) => [w wv] sv.
     by rewrite  (bij_inj bG  (uJ _ tu) (vJ _ wv)  sv).
  have : inc (Vf G t) (Vfs G u).
    by rewrite  si; apply /(Vf_image_P fg vJ); ex_tac.
  move /(Vf_image_P fg uJ) => [w wv] sv.
  by rewrite  (bij_inj bG (vJ _ tu)(uJ _ wv)  sv).
have pj: forall y, inc y (\Po I) -> exists x,
    [/\ inc x (\Po J), Vfs G x = y & cardinal x = cardinal y].
  move => y /setP_P; rewrite - tG => yG;  rewrite /J - sG.
  set x := Zo (source G) (fun z => inc (Vf G z) y).
  have xj: sub x (source G) by apply: Zo_S.
  have xj': sub x J by rewrite /J - sG.
  exists x; rewrite - (ph _ xj').
  suff : Vfs G x = y by move => ->; split => //; apply /setP_P.
  set_extens t. 
    by move /(Vf_image_P fg xj) => [u] /Zo_P [_] hh ->.
  move => ty; apply /(Vf_image_P fg xj); move: (bij_surj bG (yG _ ty)).
  by move => [a ag eq]; exists a => //; apply /Zo_P; rewrite - eq.
clear h.
set A1 :=  even_card0_sub _; set A2 := even_card0_sub _.
have qx: quasi_bij (Vfs G)  A1 A2.
  split.
   + move => s /Zo_P [] /Zo_P [] /setP_P sj a1 /set1_P a2.
     move: (pg _ sj)  (ph _ sj) => s1 s2.
     apply /Zo_P; split. 
       by apply /Zo_P;rewrite s2;split => //; apply/setP_P.
     move /set1_P => s3; case: (emptyset_dichot s) => // [] [t ts].
     empty_tac1 (Vf G t); apply /Vf_image_P => //; [ ue | ex_tac].
   + move => u v /Zo_P [] /Zo_P [] /setP_P uJ _ _.
     by move => /Zo_P [] /Zo_P [] /setP_P vJ _ _; apply: pi.
   + move => t /Zo_P [] /Zo_P [t1 t2] /set1_P t3.
     move: (pj _ t1) => [x [x5 x6 x7]].
     exists x => //; apply /Zo_P; split; first by apply /Zo_P; rewrite x7.
     by move /set1_P => xe; move: x6; rewrite xe fun_image_set0; apply: nesym.
have <- : csumb A2 (fun z => cardinal (intersectionf z f)) =
  csumb A1 (fun z => cardinal (infimum r (fun_image z g))).
  rewrite (csum_Cn2 _ qx); apply: csumb_exten.
  move => s sa; move /Zo_P: (sa) => [] /Zo_P [sb sc] /set1_P sd. 
  by rewrite pf //; apply /nonemptyP.
move ->; clear qx A1 A2.
have qx: quasi_bij (Vfs G)  (odd_card_sub J) (odd_card_sub I).
  split.
  + move => s /Zo_P [] /setP_P sj a1; move: (pg _ sj)  (ph _ sj) => s1 s2.
    by apply /Zo_P; rewrite s2;split => //; apply/setP_P. 
  + by move => u v /Zo_P [] /setP_P uJ _ /Zo_P [] /setP_P vJ _; apply: pi.
  + move => y /Zo_P [t1 t2];  move: (pj _ t1) => [x [x5 x6 x7]].
    exists x => //; apply /Zo_P; rewrite x7;split => //.
symmetry; rewrite (csum_Cn2 _ qx); apply: csumb_exten => s sa.
by move /Zo_P: (sa) => [sc sd]; move: (odd_nonempty sd) => nes; rewrite pf.
Qed.

Lemma Exercise5_5_b2 I: finite_set I ->
  cardinal (union I) +c 
       csumb (even_card0_sub I) (fun z => cardinal (intersection z))
    = csumb (odd_card_sub I) (fun z => cardinal (intersection  z)).
Proof.
move => h.
move: (Exercise5_5_b3 id h);rewrite - setU_prop.
set s1 := csumb _ _; set s2 := csumb _ _.
set s3 := csumb _ _; set s4 := csumb _ _.
have ->: s1 = s3 by apply: csumb_exten => t;  rewrite  setI_prop.
have -> //: s2 = s4 by apply: csumb_exten => t;  rewrite  setI_prop.
Qed.


(* ---- Exercise 5.6  *)


Lemma Exercise5_6  n h 
    (f := fun i => (binom h i) *c  (binom (n +c h -c i) h)):
   natp n -> natp h ->
   csumb (Nintc_even h) f = \1c +c csumb (Nintc_odd h) f. 
Proof.
move => nN hN.
have izi: inc \0c (Nintc h) by apply/(NintcP hN); apply:(cle0n hN).
set A := (Nintc_even h). 
have za: inc \0c A by apply Zo_i;[ exact:izi | apply: even_zero].
have nzc: ~ inc \0c (A -s1 \0c) by  move /setC1_P => [].
have fc0: cardinalp (f \0c) by  rewrite /f; fprops.
have nhN: natp (n +c h) by fprops.
rewrite - (setC1_K za) (csumA_setU1 _ nzc) {2} /f (binom0 hN) (cdiff_n0 nhN).
set J := (Nint h).
pose Ak k := graphs_sum_le J k.
pose Bk i := Zo (Ak n) (fun z => Vg z i <> \0c).
have cJ: cardinal J = h by rewrite card_Nint.
have fsj: finite_set J by apply:finite_Nint.
have r1: forall z (k:= cardinal z), sub z J -> nonempty z -> 
    cardinal (intersectionf z Bk) =  binom ((n +c h) -c k) h.
  move => z k zj nez.
  have ->: (intersectionf z Bk) = 
      Zo (Ak n) (fun f => forall i, inc  i z -> Vg f i <> \0c).
    set_extens v. 
      move /(setIf_P _ nez) => p1.
      move: (p1 _ (rep_i nez)) => /Zo_P [p2 p3]; apply /Zo_P;split => //.
      by move => i iz; move:  (p1 _ iz) =>  /Zo_P [_].
    move =>/Zo_P [p1 p2]; apply/(setIf_P _ nez) => j jz; apply /Zo_P;fprops.
  move: (sub_smaller zj); rewrite cJ - /k => kn.
  move: (NS_le_nat kn hN) => kN.
  set Z := Zo _ _.
  pose ga f:= Lg J (fun i => Yo (inc i z) (cpred (Vg f i)) (Vg f i)).
  pose gb f:= Lg J (fun i => Yo (inc i z) (csucc (Vg f i)) (Vg f i)).
  have pb : forall f, fgraph f -> allf f cardinalp -> domain f = J ->
       (forall i, inc i J -> natp (Vg f i)) ->
       (forall i, inc i z -> Vg f i <> \0c) ->
       csum (ga f) +c k = csum f.
    move => g p1 p2 p0 p3 p4.
    pose f2 := (graph (char_fun z J)).
    have q2: forall i, inc i J -> Vg (ga g) i +c Vg f2 i =  Vg g i.
      move => i iJ; rewrite /ga /f2 -/(Vf _ i) LgV//; Ytac zi. 
        rewrite (char_fun_V_a zj zi).
        move: (cpred_pr (p3 _ iJ)  (p4 _ zi)) => [h1 h2].
        by rewrite -(Nsucc_rw h1) - h2.
      have aux: inc i (J -s z) by apply /setC_P.
      by rewrite char_fun_V_b // csum0r //; apply: p2; rewrite p0.
    set f3 := (Lg J (Vg f2)).
    have s1: fgraph f3 by rewrite /f3; by fprops.
    have s2: sub z (domain f3) by rewrite /f3; aw.
    have s3: forall i, inc i ((domain f3) -s z) -> Vg f3 i = \0c.
      rewrite /f3/f2; aw => i ij; rewrite LgV//; last by move /setC_P: ij => [].
      by rewrite -/(Vf _ _) (char_fun_V_b zj ij).
    move: (csum_zero_unit s2 s3). 
    have ->: csumb z (Vg f3) = csumb z (fun i =>\1c).
      apply : csumb_exten => i iz;  move: (zj _ iz) => iJ;  rewrite /f3 LgV//.
      exact (char_fun_V_a zj iz).
    rewrite  csum_of_ones -/k => s5.
    move: (sum_of_sums (Vg (ga g)) (Vg f2) J); rewrite /csumb.
    have r1 : domain (ga g) = J by rewrite /ga; aw.
    have r3 :  fgraph (ga g)  by rewrite /ga; fprops.
    rewrite -{1} r1 (Lg_recovers r3) s5 => ->; f_equal.
    apply: fgraph_exten; fprops; aw; first by symmetry.
    move =>  i ij /=; rewrite LgV//; exact (q2 _ ij).
  have pa: forall f, inc f Z -> 
      [/\ k <=c n, inc (ga f) (Ak (n -c k)) & gb (ga f) = f].
    move => g /Zo_P [p0 p5].
    move /(graphs_sum_leP _ nN): (p0) => [p1 p2 p3 p4].
    have q1: forall i, inc i J -> natp (Vg g i).
      rewrite - p1 => i isf.
      exact: (NS_le_nat (cleT (csum_increasing6 (p4 _ isf) isf) p2) nN).
    move: (pb _ p3 p4 p1 q1 p5) => q3.
    have r1 : domain (ga g) = J by rewrite /ga; aw.
    have q4: k <=c csum g. 
      by rewrite - q3; apply:csum_Mle0; fprops.
    have q5: k <=c n by apply: (cleT q4 p2).
    move: (NS_diff k nN) =>q6.
    have q7: csum (ga g) <=c n -c k.
       have q4': csum (ga g) <=c csum g. 
         by rewrite - q3;  apply:csum_M0le; fprops.
       move: (NS_le_nat (cleT q4' p2) nN) => h1.
       move: p2; rewrite -q3 - {1} (cdiff_pr q5) csumC => s1.
       exact (csum_le2l kN h1 q6 s1).
    have r3 :  fgraph (ga g)  by rewrite /ga; fprops.
    have r4 : allf (ga g) cardinalp.
      red; rewrite /ga; aw => i ij; rewrite LgV//; move: (q1 _ ij) => ha; Ytac iz; fprops.
      move:  (cpred_pr ha  (p5 _ iz)) => [h1 h2]; fprops.
    have q8: inc (ga g) (Ak (n -c k)).
      apply (graphs_sum_leP _ q6); split => //; split => //.     
    split => //; rewrite /gb;apply: fgraph_exten; [ fprops | done | by aw | aw].
    move => i iJ; rewrite LgV// /ga; Ytac iz; bw => //; Ytac0; last by exact. 
    by rewrite - (proj2 (cpred_pr (q1 _ iJ) (p5 _ iz))).
  case: (cleT_el (CS_nat kN) (CS_nat nN)) => aux; last first.
     have ->: Z = emptyset.
        apply /set0_P => t tz; case: (cltNge aux (proj31 (pa _ tz))).
     rewrite  cardinal_set0 - (cdiff_pr kn); set i := h -c k.
     move: (NS_diff k hN) => iN.
     rewrite (csumC k) csumA (cdiff_pr1 (NS_sum nN iN) kN) (csumC i).
    by rewrite binom_bad //; fprops; apply: csum_Mlteq.
  have ->:  (n +c h) -c k = (n -c k) +c h.
     rewrite -{1} (cdiff_pr aux) csumC (csumC k) (csumC _ h) csumA cdiff_pr1 //.
     fprops.
  move: (proj2 (set_of_functions_sum_pr (NS_diff k nN) hN)).
  rewrite (binom_symmetric2 (NS_diff k nN) hN) -/(Ak _) => <-.
  apply /card_eqP; exists (Lf ga Z  (Ak (n -c k))); saw.
  have q6 := (NS_diff k nN).
  apply: lf_bijective.
      by move => g fa; move: (pa _ fa)=> [_ ok _].
   move => u v uz vz sw; move: (pa _ uz) (pa _ vz) => [_ _ e1][_  _ e2].
   by rewrite - e1 -e2 sw.
  move =>y yf.
  move /(graphs_sum_leP _ q6): (yf) => [p1 p2 p3 p4].
  have q1: forall i, inc i J -> natp (Vg y i).     
     rewrite - p1 => i isf.
     exact: (NS_le_nat (cleT (csum_increasing6 (p4 _ isf) isf) p2) q6).
  have q5:forall i, inc i z -> Vg (gb y)i  <> \0c.
      move =>  i iz; move: (zj _ iz) => iJ;rewrite /gb LgV//; Ytac0.
      apply: succ_nz.
  have q4: ga (gb y) = y.
      move: yf; rewrite /Ak; move /(graphs_sum_leP J q6)=> [s1 s2 s3 s4].
      rewrite /ga; apply: fgraph_exten; aww.
      move => i iJ /=; rewrite LgV// /gb LgV//; Ytac zi; Ytac0; last by exact.
      by apply: cpred_pr2; apply: q1.
  have q2: fgraph (gb y) by rewrite /gb; fprops.
  have dgb: (domain (gb y)) = J by rewrite /gb; aw.
  have q7: forall i, inc i J -> natp (Vg (gb y) i).
    move => i ij; move: (q1 _ ij) => ha;rewrite /gb LgV//; Ytac zi; fprops.
  have q3: (allf (gb y) cardinalp).
      move => i; rewrite dgb => ij; rewrite /gb LgV//; move: (q1  _ ij) => hw.
      Ytac zi; fprops.
  exists (gb y) => //.
  apply /Zo_P;split => //;  apply /(graphs_sum_leP _ nN) => //;split => //.
    move: (pb _ q2 q3 dgb q7 q5); rewrite q4; move => <-.
    rewrite  - (cdiff_pr aux) csumC; apply: csum_Mlele => //; fprops.
set fct0:= cst_graph J \0c.
have fct0_ok: inc fct0 (Ak n).
   apply /graphs_sum_leP => //; rewrite /fct0 Lgd;split => //.
       by rewrite -/(csumb _ _) csum_of_same cprod0l;apply:cle0n.
     fprops.
   hnf; aw; move => t tj; rewrite LgV//; fprops.
have ue: (unionf J Bk) = Ak n -s1 fct0.
   set_extens t.
     move => /setUf_P [z tz] /Zo_P [ta tb].
     apply /setC1_P; split => //; dneg eq2; rewrite eq2 /fct0 LgV//.
   move => /setC1_P [t1 t2]; apply /setUf_P.
   move /(graphs_sum_leP _ nN): (t1) => [t4 _ t5 t6].
   suff: (exists2 i, inc i J &  Vg t i <> \0c).
     move => [i ij t3]; ex_tac; apply /Zo_P;split => //.
   ex_middle bad; case: t2; rewrite /fct0. 
   apply: fgraph_exten => //; aww.
   rewrite t4; move => s st /=; rewrite LgV//; ex_middle ok; case: bad; ex_tac.
move: (Exercise5_5_b3 Bk fsj).
have cb1: cardinalp (binom (n +c h) h) by apply: CS_nat; apply:NS_binom.
move: (csucc_pr2 fct0_ok); rewrite -ue csucc_pr4; last by fprops.
rewrite csumC (cprod1l cb1) (binom_symmetric2 nN hN).
rewrite (proj2 (set_of_functions_sum_pr nN hN)) => ->.
set s1 := csumb _ _;set s2 := csumb _ _.
set s3 := csumb _ _; set s4 := csumb _ _.
have ->: s2 = s4.
  have ->: s2 = csumb (odd_card_sub J) 
        (fun z => binom ((n +c h) -c (cardinal z)) h).
    apply: csumb_exten => t.
    move => /Zo_P []  /setP_P ta tb; apply: r1 => //. 
    by apply: odd_nonempty.
  set X := (odd_card_sub J); set F := Nintc_odd h.
  have pa: (forall x, inc x X -> inc (cardinal x) F).
    move => x /Zo_P [] /setP_P pa pb; apply /Zo_P;split => //.  
    apply /(NintcP hN); rewrite - cJ; apply:(sub_smaller pa). 
  rewrite (card_partition_induced1 _ pa).
  apply: csumb_exten => i iF.
  set Y:= Zo _ _.
  transitivity (csumb Y (fun _ => (binom ((n +c h) -c i) h))).
    by  apply: csumb_exten => j jY /=; move /Zo_P: jY => [_ ->].
  rewrite csum_of_same cprodC - cprod2cl.
  move /Zo_P: iF => [i1 i2]; move: (Nint_S i1) => i3.
  have ->: Y = subsets_with_p_elements i J.
     set_extens t.
       move => /Zo_P [] /Zo_P [t1 t2] t3; apply /Zo_P;split => //.
     move => /Zo_P [t1 t2]; apply/Zo_P;split => //.
     by apply /Zo_P;split => //;  rewrite t2. 
  by rewrite  (card_p_subsets hN i3 cJ).
have ->: s1 = s3.
   have ->: s1 = csumb (even_card0_sub J) 
        (fun z => binom ((n +c h) -c (cardinal z)) h).
     apply:csumb_exten => t.
     by move => /setC1_P [/Zo_P[/setP_P ta tb]] /nonemptyP tne; apply: r1.
   set X := (even_card0_sub J); set F :=  (A -s1 \0c).
   have pa: (forall x, inc x X -> inc (cardinal x) F).
      move => x /setC1_P [/Zo_P[/setP_P wJ pa]] pb; apply /Zo_P; split.
         apply /Zo_P;split => //;apply /(NintcP hN). 
         rewrite - cJ; apply:(sub_smaller wJ). 
     by move /set1_P=> /card_nonempty.
   rewrite (card_partition_induced1 _ pa).
   apply: csumb_exten => i iF.
   set Y:= Zo _ _.
   transitivity (csumb Y (fun _ => (binom ((n +c h) -c i) h))).
     by apply: csumb_exten => j jY /=; move /Zo_P: jY => [_ ->].
   rewrite csum_of_same cprodC - cprod2cl.
   move /Zo_P: iF => [] /Zo_P [i1 i2] /set1_P i3; move: (Nint_S i1) => i4.
   have ->: Y = subsets_with_p_elements i J.
     set_extens t. 
       by move => /Zo_P [] /Zo_P [] /Zo_P [t1 t2] t3 t4; apply /Zo_P.
     move => /Zo_P [t1 t2]; apply/Zo_P;split => //; apply /Zo_P;split => //. 
       by apply /Zo_P;split => //; rewrite t2.
     by move => /set1_P => te; case: i3; rewrite - t2 te cardinal_set0.
   by rewrite (card_p_subsets hN i4 cJ).
by rewrite (csumC s3) - csumA => ->.
Qed.


(* ---- Exercise 5.7  *)


Definition nbsurj n p := 
   cardinal(surjections (Nint n)  (Nint p)).

Lemma nbsurj_pr E F:
  finite_set E -> finite_set F -> 
  cardinal (surjections  E F) = nbsurj (cardinal E) (cardinal F).
Proof.
move => /NatP  nN /NatP mN.
apply/card_eqP.
set n :=  (cardinal E); set m := (cardinal F).
set s:= (surjections E F);set t := surjections _ _.
move/card_eqP:(card_Nint nN) => [g [fg sg tg]].
move/card_eqP:(card_Nint mN) => [h [fh sh th]].
move: (inverse_bij_fb fh) => bih.
set j := (fun f => (inverse_fun h) \co f \co g).
have pc: forall f, inc f s ->
  (inverse_fun h \coP f)/\  (inverse_fun h \co f) \coP g.
  move => f /Zo_P [] /functionsP [ff sf tf] sjf.
  have s1: inverse_fun h \coP f by split => //; aw; try fct_tac; ue.
  split => //; split => //; aw; try ue; try fct_tac.  
exists (Lf (fun f => (inverse_fun h) \co f \co g) s t).
saw;apply: lf_bijective.
    move => f fp; move: (pc _ fp)=> [s1 s2]; apply/ Zo_P;split => //.
      apply /functionsP;red;saw; fct_tac.
      move/ Zo_hi: fp => sjf.
    move: (compose_fs sjf (proj2 bih) s1) => s3; apply:compose_fs => //.
    exact (proj2 fg).
  move => u v us vs; move:  (pc _ us) (pc _ vs)=> [s1 s2][s3 s4] s5.
  move: (compf_regl fg s2 s4 s5) => s6.
  by move: (compf_regr bih s1 s3 s6).
move => y /Zo_P []/functionsP [fy sy ty] sjy.
set f := (h \co (y \co inverse_fun g)).
move: (inverse_bij_fb fg) => big.
have s1: (y \coP inverse_fun g) by saw; try fct_tac; ue.
have s2: h \coP (y \co inverse_fun g) by saw; try ue; try fct_tac.
have fs: inc f s.
  apply/ Zo_P; split. 
    by rewrite /f;apply /functionsP;saw;try fct_tac.
  move: (compose_fs (proj2 big) sjy s1) => s3; apply:compose_fs => //.
  exact (proj2 fh).
exists f => //; rewrite /f (compfA (composable_inv_f fh) s2).
have pd: (source h) = target  (y \co inverse_fun g) by aw; ue.
  rewrite (bij_left_inverse fh) pd (compf_id_l (proj32 s2)).
rewrite - (compfA s1 (composable_inv_f fg)) (bij_left_inverse fg) sg - sy.
by symmetry;apply (compf_id_r).
Qed.

Lemma nbsurj_inv n p: natp n -> natp p ->
  p ^c n = csumb (Nintc p) (fun k => (binom p k) *c (nbsurj n k)).
Proof.
move => nN pN.
set I := (Nint n); set J:= (Nint p).
have ci: n = cardinal I by rewrite (card_Nint nN).
have cj: p = cardinal J by rewrite (card_Nint pN).
set K :=  (Nintc p).
have ->: p ^c n = cardinal (functions I J).
  by rewrite ci cj; apply:cpow_pr; aw.
have pa: forall x, inc x (functions I J) ->  sub (Imf x) J.
  by move => x /functionsP [p1 p2 <-]; apply:Imf_Starget.
have pb: forall x, inc x (functions I J) ->
   inc (cardinal (Imf x)) K.
   move => x h; move: (sub_smaller (pa _ h)). 
   by rewrite - cj; move /(NintcP pN).
rewrite (card_partition_induced pb); apply: csumb_exten => k.
move/(NintcP pN) => kp.
move: (NS_le_nat kp pN) => kN.
rewrite - (card_p_subsets pN kN (sym_eq cj)). 
set E1 := Zo _ _; set K1 := subsets_with_p_elements _ _.
have pc: forall c, inc c E1 -> inc (Imf c) K1.
  by move => c /Zo_P [pc pd]; apply /Zo_P;split => //; apply /setP_P; apply: pa.
pose phi := Lf Imf E1 K1.
have sphi: E1 = source phi by rewrite /phi; aw.
have tphi: K1 = target phi by rewrite /phi; aw.
have fphi: function phi by apply: lf_function. 
rewrite sphi tphi; apply: (shepherd_principle fphi).
move => tf; rewrite - tphi; move /Zo_P => [] /setP_P tfj ctf.
set K2:= Zo (functions I J) (fun f => Imf f = tf).
have ->: Vfi1  phi tf = K2.
  set_extens t.  
     move /(iim_fun_set1_P _ fphi) => []; rewrite - sphi /phi => t1.
     rewrite LfV//.  move /Zo_P: t1 => [t1 t2] t3; apply /Zo_P;split => //.
  move => /Zo_P [t1 t2]; apply /(iim_fun_set1_P _ fphi); rewrite - sphi.
  have te1: inc t E1 by apply /Zo_P; rewrite t2.
  by rewrite /phi LfV//.
rewrite ci - ctf.
rewrite - nbsurj_pr;  try apply/NatP; [  |  by rewrite - ci | by rewrite ctf].
apply /card_eqP.
exists (Lf restriction_to_image K2 (surjections I tf)); saw.
apply: lf_bijective.
    move => c /Zo_P [] /functionsP [qa qb qc] qd; apply /Zo_P.
    move: (restriction_to_image_fs qa) => qe;split => //; apply /functionsP.
    move: (proj1 qe) => f.
    by hnf;rewrite{2 3} /restriction_to_image /restriction2; aw; split.
  move => u v  /Zo_P [] /functionsP [qa qb qc] qd.
  move => /Zo_P [] /functionsP [ra rb rc] rd sr.
  apply: function_exten => //; rewrite ? rb ? rc // => x xI.
  move: (f_equal (Vf ^~x) sr). 
  move: (restriction_to_image_axioms qa) => h; rewrite restriction2_V //.
  move: (restriction_to_image_axioms ra) => h'; rewrite restriction2_V //.
  by rewrite rb - qb.
move => y /Zo_P [] /functionsP [qa qb qc] qd.
set f := Lf (Vf y) I J.
have fa: forall z, inc z I  -> inc (Vf y z) J.
    rewrite -qb; move => z zi; apply: tfj; rewrite -qc; Wtac.
have fb: function f by apply: lf_function.
have sfi: source f = I by rewrite /f;aw.
have fc: Imf f = tf.
  set_extens t. 
    move /(Imf_P fb); rewrite sfi; move => [u u1 ->]; rewrite /f LfV//.
    Wtac.
  rewrite -qc => tt; move: (proj2 qd _ tt); rewrite qb; move => [u u1 u2].
  by apply /(Imf_P fb); rewrite sfi;ex_tac; rewrite /f LfV.
have fd:inc f K2 by apply/ Zo_P;split => //;apply/functionsP;rewrite /f;red;aw.
have ra:= (proj1 (restriction_to_image_fs fb)).
have rb:= (restriction_to_image_axioms fb).
have sr:source (restriction_to_image f) = source y by rewrite corresp_s sfi.
ex_tac; apply: function_exten => //.
  by rewrite corresp_t fc. 
by rewrite qb;move => t ts; rewrite restriction2_V // -? sfi // /f? LfV//; aw.
Qed.

Lemma nbsurj_rec n p: natp n -> natp p ->
  nbsurj (csucc n)(csucc p) = 
   (csucc p) *c ( nbsurj n p +c  nbsurj n (csucc p)).
Proof.
move => nN pN; rewrite {1} /nbsurj csumC.
move: (NS_succ pN) => spN.
set I := (Nint (csucc n)); set J:= (Nint (csucc p)).
set I' := Nint n.
set E :=  (surjections I J).
pose phi := Lf (fun f => Vf f n) E J.
have sphi: E = source phi by rewrite /phi; aw.
have pa: csucc p = cardinal (target phi). 
  by rewrite /phi; aw; rewrite  (card_Nint spN).
rewrite {1} pa sphi; clear pa.
have lfa: lf_axiom (Vf ^~n) E J.
  move => f /Zo_P [] /functionsP [pa pb pc] _.
  by Wtac; rewrite pb; apply:Nint_si.
have fphi: function phi by apply: lf_function. 
apply:(shepherd_principle fphi).
rewrite {1} /phi; aw; move => x xJ.
set F := Vfi1 phi x.
have fp: forall f, inc f F <-> inc f (surjections I J) /\ x = Vf f n.
  move => f; split.
    move /(iim_fun_set1_P _ fphi) => []; rewrite - sphi => fe. 
    rewrite{1}/phi LfV//.
   move => [pa pb]; apply /(iim_fun_set1_P _ fphi).
   split => //;[ ue | rewrite /phi LfV//].
pose sfx f := exists2 y, inc y I' & Vf f y = x.
have ii': sub I' I by apply: Nint_M.
set A1 := Zo F sfx. 
have <-: cardinal A1 = nbsurj n (csucc p).
  apply /card_eqP.
  exists (Lf (restriction^~ I' ) A1 (surjections I' J)); saw.
  apply /lf_bijective.
      move => f /Zo_P [] /fp [] /Zo_P [] /functionsP [ff sf tf] sjf fn sff.
      have si: sub I' (source f) by rewrite sf.
      move: (restriction_prop ff si); rewrite tf => fp'.
      apply /Zo_P; split; first by apply /functionsP.
      move: fp' => [sa sb sc]; split; first by exact.
      rewrite sc sb - tf=> y ytf; move: (proj2 sjf _ ytf) => [a asf va].
      move: asf; rewrite sf; move /(NintsP nN) => lean.
      case: (equal_or_not a n) => lan.
        move: sff => [b ba bb]; rewrite va lan - fn - bb; ex_tac.
        rewrite restriction_V //.
      have aI: inc a I' by  apply /(NintP nN).
      by exists a => //; rewrite restriction_V.
    move => f g /Zo_P [] /fp [] /Zo_P [] /functionsP [ff sf tf] sjf fn sff.
    move => /Zo_P [] /fp [] /Zo_P [] /functionsP [fg sg tg] sjg gn sfg sr.
    apply: function_exten => //; (try ue); move => i isf /=.
    move: isf; rewrite sf; move /(NintsP nN) => lein.
    case: (equal_or_not i n) => lin; first by rewrite lin - fn gn.
    have iI: inc i I' by  apply /(NintP nN); split.
    have si: sub I' (source f) by rewrite sf.
    have sj: sub I' (source g) by rewrite sg - sf.
    move: (f_equal (Vf^~ i) sr); rewrite restriction_V //  restriction_V //.
  move => y /Zo_P [] /functionsP [fy sy ty] sjy.
  move: (Nint_pr4 nN); rewrite -/I -/I' - sy; move => [ci pa].
  move:(extension_fs x fy pa sjy) => sjf.
  have pb: sub I' (source (extension y n x)). 
       by rewrite /extension sy; aww.
  move:(proj1 sjf) => fjf.
  have si: source (extension y n x) = I by rewrite /extension; aw.
  have ti: target (extension y n x) = J.
    rewrite /extension ty; aw; rewrite setU1_eq //.
  have fx: Vf (extension y n x) n = x by rewrite extension_Vf_out.
  have re : (restriction (extension y n x) I') = y.
  move: (restriction_prop fjf pb) => [pc pd pe].
  apply : function_exten => //; rewrite ? pd ?pe ? ti//.
  move => i ii /=;rewrite restriction_V //.
    by rewrite extension_Vf_in // sy.
  have aux: sfx (extension y n x).
     rewrite -ty in xJ; move: (proj2 sjy _ xJ) => [s sa sb]. 
     exists s; [ ue | rewrite extension_Vf_in //]. 
   exists (extension y n x);last by ue.
  by apply:Zo_i=> //;apply /fp; split => //; apply:Zo_i=> //; apply /functionsP.
have sa1: sub A1 F by apply: Zo_S.
rewrite (cardinal_setC2 sa1) csum2cl - csum2cr; congr (_ +c _).
have pa: n = cardinal I' by rewrite (card_Nint nN).
have fs1: finite_set I' by apply:finite_Nint.
have pb: p = cardinal (J -s1 x). 
  by rewrite - (cpred_pr5 xJ) (card_Nint spN) cpred_pr2.
have fs2: finite_set (J -s1 x) by apply/NatP;rewrite -pb.
rewrite pa pb - (nbsurj_pr fs1 fs2).
apply /card_eqP.
have pc: forall f, inc f (F -s A1) -> restriction2_axioms f I' (J -s1 x). 
  move => f /setC_P [fF fp1]. 
  move: (fF) => /fp [] /Zo_P[] /functionsP [ff sf tf] sjf fn.
  have aux: sub I' (source f) by ue.
  red; rewrite sf tf; split => //; try apply: sub_setC.
  move => i /(Vf_image_P ff aux) [u ui ->]; apply /setC1_P; split.
      rewrite -tf; Wtac.
  by dneg fa1; apply /Zo_P;split => //; exists u.
exists (Lf (fun z => restriction2 z I' (J -s1 x))
  (F -s A1) (surjections I' (J -s1 x))); saw.
apply /lf_bijective.
    move => f fa /=; move: (pc _ fa) => a1.
    move: (restriction2_prop a1) => a2.
    move: fa => /Zo_P [] /fp [] /Zo_P [] /functionsP [ff sf tf] sjf fn sff.
    apply /Zo_P;split; first by apply /functionsP.
    move: a2 => [a3 a4 a5]; split; first by exact.
    rewrite a4 a5 - {1} tf=> y /setC1_P [ytf xx]. 
    move: (proj2 sjf _ ytf) => [a asf va].
    move: asf; rewrite sf; move /(NintsP nN) => lean.
    case: (equal_or_not a n) => lan; first by case: xx; rewrite fn va lan.
    have aI: inc a I' by  apply /(NintP nN); split.
    by exists a => //; rewrite restriction2_V. 
  move => f g fa fb sr.
  move: (pc _ fa) (pc _ fb) => a1 a2.
  move: fa => /setC_P [] /fp [] /Zo_P [] /functionsP [ff sf tf] _ fv _.
  move: fb => /setC_P [] /fp [] /Zo_P [] /functionsP [fg sg tg] _ gv _.
  apply: function_exten => //; (try ue); move => i isf /=.
  move: isf; rewrite sf; move /(NintsP nN) => lein.
  case: (equal_or_not i n) => lin; first  by rewrite lin - fv gv.
  have iI: inc i I' by  apply /(NintP nN); split.
  move: (f_equal (Vf^~ i) sr); rewrite restriction2_V // restriction2_V //.
move => y /Zo_P [] /functionsP [fy sy ty] sjy.
move: (Nint_pr4 nN); rewrite -/I -/I' - sy; move => [ci pd].
move:(extension_fs x fy pd sjy) => sjf.
have pe: sub I' (source (extension y n x)). 
  by rewrite /extension sy; aww.
move:(proj1 sjf) => fjf.
have si: source (extension y n x) = I by rewrite /extension; aw.
have ti: target (extension y n x) = J.
by rewrite /extension ty; aw; apply:setC1_K.
have fx: Vf (extension y n x) n = x by rewrite extension_Vf_out.
move: (extension_restr x fy pd); rewrite ty => pf.
exists (extension y n x) => //; apply/setC_P; split.
  by apply /fp; split => //; apply /Zo_P; split => //; apply /functionsP.
move /Zo_P => [sa [z]]; rewrite - sy => sb;rewrite extension_Vf_in // => pg.
by move: (Vf_target fy sb); rewrite pg ty => /setC1_P [].
Qed.

Definition extension_p2 g :=  extension_to_parts (extension_to_parts g).
Definition extension_p3 g := Vfs (extension_to_parts g).


Lemma ext2_pr1 g E z:
  function g ->  source g = E -> inc z (\Po (\Po E)) -> 
  extension_p3 g z =  Vf (extension_p2 g) z.
Proof.
move => ha hb /setP_P zi.
by rewrite  (etp_V (proj31 (etp_f (proj31 ha)))) // lf_source hb.
Qed.

Lemma ext2_pr2 g E E' z: 
  (bijection_prop g E E') -> inc z (\Po (\Po E)) -> 
  extension_p3 g z =  Vf (extension_p2 g) z.
Proof. by move => [[[ha _] _] hb] hc; apply:ext2_pr1. Qed.

Lemma ext2_pr3 E E' g z: 
  bijection_prop g E E' -> inc z (\Po (\Po E)) ->
  forall t,
  (inc t (extension_p3 g z) <-> 
     exists2 u, inc u z & t = (Vfs g u)).
Proof.
move => [pa pb pc]  /setP_P zz t.
have fg := (proj1 (proj1 pa)).
have cg := (proj31 fg).
have pe: sub z (source (extension_to_parts g)) by rewrite lf_source pb.
split.
  move/(Vf_image_P (etp_f cg) pe) => [u ua ->].
  have sug: sub u (source g) by rewrite pb; apply /setP_P; apply: zz.
  rewrite (etp_V cg sug); ex_tac. 
move => [u uz ->].
have sug: sub u (source g) by rewrite pb; apply /setP_P; apply: zz.
rewrite - (etp_V cg sug); apply /(Vf_image_P (etp_f cg) pe); ex_tac.
Qed.


Lemma ext2_pr5 E E' g z: 
  bijection_prop g E E' -> inc z (\Po (\Po E)) ->
  inc (extension_p3 g z) (\Po (\Po E')).
Proof.
move => bg zz; apply/setP_P  => t /(ext2_pr3 bg zz) [u uz ->].
move:(bg) => [[[fg _] _] _ <-].
apply/setP_P; apply:(fun_image_Starget1 fg).
Qed.

Lemma ext2_pr6 E E' E'' g g' z:
  bijection_prop g E E' -> bijection_prop g' E' E'' ->
  inc z (\Po (\Po E)) ->
  extension_p3 g' (extension_p3 g z) = extension_p3 (g' \co g) z.
Proof.
move => ha hb zz.
have hc:=(compose_bp ha hb).
move:(ha) (hb)=> [ha1 ha2 ha3] [hb1 hb2 hb3].
move: (ext2_pr5 ha zz); rewrite (ext2_pr2 ha zz) => hd.
have he: composableC g' g. 
   by apply: composable_for_function;split; try fct_tac; rewrite ha3.
have hf:composableC (extension_to_parts g') (extension_to_parts g).
  have ra:=(proj31 (etp_f (proj31 (proj1 (proj1 ha1))))).
  have rb:=(proj31 (etp_f (proj31 (proj1 (proj1 hb1))))).
  by split => //; rewrite lf_source lf_target hb2 ha3.
have zz': inc z (source (extension_to_parts (extension_to_parts g))).
  by rewrite !lf_source ha2.
rewrite (ext2_pr2 hc zz)  (ext2_pr2 hb hd).
rewrite /extension_p2 (etp_compose he) etp_compose // compfV//.
by apply:etp_composable.
Qed.

Lemma ext2_pr7 E E' g z:
  bijection_prop g E E' ->
  inc z (\Po (\Po E)) ->
  extension_p3 (inverse_fun g) (extension_p3 g z) = z.
Proof.
move => ha zz; move: (ha) => [hb hc _].
rewrite (ext2_pr6 ha (inverse_bij_bp ha) zz) (bij_left_inverse hb) hc.
have ip:= (identity_bp E).
by rewrite (ext2_pr2 ip zz) /extension_p2 etp_identity etp_identity idV.
Qed.

Lemma ext2_pr8 E E' g z:
  bijection_prop g E E' ->
  inc z (partitions E) -> inc (extension_p3 g z) (partitions E').
Proof.
move => pa /Zo_P [ha [[hb hc] hd]].
move:(pa) => [[[fg ig] [_ sjg]] sg tg].
move/setP_P: (ha) => ha'.
have K a b:  inc b z -> inc a b -> inc a (source g).
  by move => sa sb; rewrite sg - hb; union_tac.
have H x: inc x z -> forall y,
   inc y (Vfs g x) <-> (exists2 u, inc u x & y = Vf g u).
  move => /ha' /setP_P; rewrite - sg => tt.
  exact:(Vf_image_P fg tt).
apply: (Zo_i (ext2_pr5 pa ha)); split; last first.
  move => t /(ext2_pr3 pa ha)  [u uz ->]. 
  move:(hd _ uz) => [v vu]; exists (Vf g v); apply/(H _ uz); ex_tac.
split => //.
  set_extens t. 
    move/setU_P => [y yz /(ext2_pr3 pa ha)  [u uz yv]].
    move: yz; rewrite yv => /(H _ uz) [w /(K _ _ uz) wu ->]; Wtac.
  rewrite - tg => /sjg [x xsg ->]; apply /setU_P.
  move: xsg; rewrite sg - hb => /setU_P [v xv vz].
  exists (Vfs g v); first by apply/(H _ vz); ex_tac.
   by apply/(ext2_pr3 pa ha); ex_tac.
move => a b /(ext2_pr3 pa ha) [u uz ->] /(ext2_pr3 pa ha) [v vz ->].
case: (hc _ _ uz vz) => uv; [  by rewrite uv; left | right ].
apply: disjoint_pr => x /(H _ uz) [u' uu' ->] /(H _ vz) [v' vv' ea]. 
by empty_tac1 u'; rewrite (ig _ _ (K _ _ uz uu') (K _ _ vz vv') ea).
Qed.

Lemma ext2_pr9 E E' g z z':
  bijection_prop g E E' ->
  inc z (partitions E) -> inc z' (partitions E) ->
  (extension_p3 g z) = (extension_p3 g z') -> z = z'.
Proof.
move => ha /Zo_S hb /Zo_S hc ea.
by rewrite - (ext2_pr7 ha hb) - (ext2_pr7 ha hc) ea.
Qed.

Definition partitionsx E p :=
  Zo (partitions E) (fun z => cardinal z = p).

Definition nbpart n p :=
  cardinal(partitionsx (Nint n) p).

Lemma nbpart_pr1 E F g p:
  bijection_prop g E F ->
  bijection (Lf (extension_p3 g)  (partitionsx E p)(partitionsx F p)).
Proof.
move => pg.
have T: forall X X' f z, bijection_prop f X X' -> 
   inc z  (partitionsx X p) -> inc (extension_p3 f z)  (partitionsx X' p).
  move => X X' f z h /Zo_P [zp cz]; apply/Zo_P; split.
    apply: (ext2_pr8 h zp).
  rewrite - cz; symmetry; apply /card_eqP.
  exists (Lf ( Vf (extension_to_parts f)) z (extension_p3 f z)).
  move:(h) => [ha1 ha2 ha3].
  have fg := (proj1 (proj1 ha1)).
  have cg := (proj31 fg). move: (etp_f cg) => ef.
  move:(zp) => /Zo_P [/setP_P qa qb].
  have sz: sub z (source (extension_to_parts f)) by rewrite lf_source ha2. 
  hnf; saw; apply:lf_bijective.
  - move => t tz; apply/(Vf_image_P ef sz); ex_tac.
  - by move => u v uz vz; apply: (proj2 (etp_fi (proj1 ha1))); apply: sz. 
  - by move => y /(Vf_image_P ef sz). 
apply: lf_bijective.
- by move => z; apply:T.
- by move => u v /Zo_S ha /Zo_S hb; apply:(ext2_pr9 pg).
- move => y yp.
  move:(T _ _ _ _ (inverse_bij_bp pg) yp) => xi; ex_tac.
  rewrite -{1} (ifun_involutive (proj1 (proj1 (proj31 pg)))).
  symmetry; apply: (ext2_pr7 (inverse_bij_bp pg) (Zo_S (Zo_S yp))).
Qed.

Lemma nbpart_pr E p:
  finite_set E -> cardinal (partitionsx E p) = nbpart (cardinal E) p.
Proof.
move => fse; set n :=  (cardinal E).
have : n = cardinal (Nint n) by rewrite card_Nint //; apply /NatP.
move/card_eqP => [g gp]; apply /card_eqP.
exists (Lf (extension_p3 g) (partitionsx E p) (partitionsx (Nint n) p)).
hnf; saw; apply: (nbpart_pr1 p gp).
Qed.

Lemma nbsurj_part n p: natp n -> natp p ->
  nbsurj n p = (factorial p) *c (nbpart n p).
Proof.
move => nN pN.
rewrite  /nbsurj /nbpart.
set I := (Nint n); set J:= (Nint p).
have cj: p = cardinal J by rewrite  (card_Nint pN).
set E :=  (surjections I J).
set K := (partitionsx I p).
pose f g := fun_image J (fun z => Vfi1 g z).
have lfa: lf_axiom f E K.
  move => g /Zo_P [] /functionsP [fg sg tg] sjg.
  have p1: inc (f g) (\Po (\Po I)).
     apply /setP_P => z /funI_P [w wJ ->]; apply /setP_P => t.
     by move /(iim_fun_set1_P w fg) => []; rewrite sg.
  have p2: cardinal (f g) = p.
    symmetry; rewrite cj; apply /card_eqP.
    exists (Lf (fun z => Vfi1 g  z) J (f g)).
    saw; apply lf_bijective.
        move => z zj; apply /funI_P; ex_tac.
      move => u v uj vj si.
      rewrite -tg in uj; move: (proj2 sjg _ uj) => [x xsg h].
      move: (iim_fun_set1_i fg xsg h); rewrite si => xi.
      by rewrite  (iim_fun_set1_hi fg xi) - h.
    by move => y /funI_P.
  have p3: union (f g) = I.
    set_extens t.
      move =>/setU_P [z tz h]; move /setP_P: p1 => h1. 
      by move: (h1 _ h) => /setP_P; apply.
    move => ti; apply /setU_P; exists (Vfi1 g (Vf g t)).
    rewrite - sg in ti.
       by exact: (iim_fun_set1_i fg ti (refl_equal  (Vf g t))).
    apply /funI_P; exists (Vf g t) => //; rewrite -tg; Wtac.
  have p4: alls (f g) nonempty.
     move => z /funI_P [t]; rewrite - tg => ttg ->.
     move: (proj2 sjg _ ttg) => [x xsg h].
     move: (iim_fun_set1_i fg xsg h) => h1; ex_tac.
  apply /Zo_P; split => //; apply:Zo_i => //;split => //; split => //. 
  move => a b a1 b1; mdi_tac nab => u ua ub; case: nab; move: ua ub.
  move /funI_P: a1 => [z zj ->]; move /funI_P: b1 => [w wj ->].
  by move => h1 h2;rewrite (iim_fun_set1_hi fg h1) - (iim_fun_set1_hi fg h2).
pose phi := Lf f E K.
have sphi: E = source phi by rewrite /phi; aw.
have ->: K = target phi by rewrite /phi; aw.
have fphi: function phi by apply: lf_function. 
rewrite sphi cprodC; apply: (shepherd_principle fphi).
rewrite {1} /phi; aw; move => x xK.
set F := Vfi1 phi x.
have fp: forall g, inc g F <-> inc g (surjections I J) /\ f g = x.
  move => g; split.
    move /(iim_fun_set1_P _ fphi) => []; rewrite - sphi => fe;rewrite{1}/phi.
    rewrite LfV//; move => pa;split => //.
  move => [pa pb]; apply /(iim_fun_set1_P _ fphi).
  by split => //;[ ue | rewrite /phi LfV//].
move: (xK) => /Zo_P [px]; rewrite cj.
move /card_eqP => [fa [bfa sfa tfa]].
move /Zo_hi: px => [[pa pb] pc].
pose fb t := select (inc t) x.
have prb: forall t, inc t I -> inc t (fb t) /\ inc (fb t) x.
  move => t ti; apply: (select_pr). 
    move: ti; rewrite - pa => /setU_P [z za zb]; ex_tac.
  move => a b sa sb sc sd; case: (pb _ _ sa sc) => // h; empty_tac1 t.
pose fc := Lf (fun t => (Vf fa (fb t))) I J.
have sfc: source fc = I by rewrite /fc; aw.
have tfc: target fc = J by rewrite /fc; aw.
have fc0:  lf_axiom  (fun t => (Vf fa (fb t))) I J.
   move=> t ti; move: (prb _ ti) => [_]; rewrite - sfa - tfa => h; Wtac;fct_tac.
have fc1:  function fc by apply: lf_function.
have fc2': surjection fc.
  split => // y; rewrite /fc; aw; rewrite - tfa => yJ.
  move: (bij_surj bfa yJ); rewrite sfa; move => [z zx ->].
  move: (pc _ zx) => [t tz].
  have ti: inc t I by rewrite - pa; union_tac.
  rewrite tfa;ex_tac; rewrite LfV//.
  move: (prb _ ti) => [sa sb]; case: (pb _ _ zx sb); first by move => ->.
  move => h; empty_tac1 t.
have fc2: inc fc (surjections I J).
  apply /Zo_P; split => //; by apply /functionsP.
have fc3: forall w, inc w x -> Vfi1 fc (Vf fa w) = w.
  move => w wx; set_extens s. 
    move /(iim_fun_set1_P _ fc1); rewrite sfc /fc; move => [ta]; rewrite LfV//.
    move => vfa; move: (prb _ ta) => [tb tc].
    by rewrite - sfa in wx tc; rewrite (bij_inj bfa  wx tc vfa).
  move => sw; apply /(iim_fun_set1_P _ fc1). 
  have si: inc s I by rewrite - pa; union_tac.
  rewrite sfc /fc LfV//;split => //; move: (prb _ si) => [tb tc].
  case: (pb _ _ wx tc); [by move => <- | by move  =>h; empty_tac1 s].
have fc4: inc fc F.
  move: (proj1 (proj1 bfa)) => ffa.
  apply /fp; split => //; rewrite /f;set_extens t.
    move /funI_P => [z zJ ->]; rewrite -tfa in zJ.
    move: (bij_surj bfa  zJ); rewrite sfa; move => [w wx ->].
    by rewrite  (fc3 _ wx).
  move => tx; apply /funI_P; exists (Vf fa t); first by Wtac.
  by rewrite (fc3 _ tx).
rewrite - (card_permutations (finite_Nint p)). 
symmetry;  apply /card_eqP.
exists (Lf (fun z => z \co fc) (permutations J) F); saw.
move /Zo_P: (fc2) => [sa sb]; move: (exists_right_inv_from_surj sb) => [s sc]. 
apply /lf_bijective.
    move => g /Zo_P [] /functionsP [fg sg tg] big.
    have gfc: g \coP fc by split => //; rewrite sg tfc.
    have fgfc: function (g \co fc) by fct_tac.
    have tgfc: target (g \co fc) = J by aw.
    have sgfc: source (g \co fc) = I by aw.
    have ssgfc: surjection(g \co fc) by apply/compose_fs =>//;exact (proj2 big).
    have pa':inc (g \co fc) (surjections I J).
     apply /Zo_P; split; first by  apply/functionsP;aw.
     by apply /compose_fs => //; exact (proj2 big).
    have aux2: forall w, inc w I ->
      (Vfi1 (g \co fc) (Vf (g \co fc) w)) = (Vfi1 fc (Vf fc w)).
      move => w wi; set_extens t.
        move /(iim_fun_set1_P _ fgfc); rewrite sgfc; move => [tI]. 
        rewrite - sfc in wi tI; rewrite  ! compfV//.
        move: (Vf_target fc1 wi) (Vf_target fc1 tI); rewrite tfc - sg.
        move => i1 i2 i3; rewrite  (bij_inj big i1 i2 i3).
        by apply:  (iim_fun_set1_i fc1 tI).
      rewrite - sfc in wi; move /(iim_fun_set1_P _ fc1) => [ta tb]. 
      rewrite compfV //; apply:(iim_fun_set1_i fgfc); aw; trivial.
      rewrite compfV//; ue.
    move /fp: fc4 => [_] xv1.
    apply /fp;split => //; set_extens t.
      move /funI_P => [z zJ ->].
      rewrite -tgfc in zJ; move: (proj2 ssgfc _ zJ); rewrite sgfc.
      move => [a ai ->]; rewrite (aux2 _ ai) - xv1.
      apply /funI_P;exists (Vf fc a) => //; Wtac.
    rewrite -xv1; move /funI_P => [z zj etc].
    apply /funI_P; rewrite -tfc in zj; move: (proj2 fc2' _ zj) etc.
    move => [a]; rewrite sfc => s1 ->; rewrite - (aux2 _ s1) => ->.
    exists (Vf (g \co fc) a) => //; rewrite - tgfc; Wtac.
  move => u v up vp sv; move: sc => [sc sd].
  move: up vp sa => /Zo_P [] /functionsP [fu su tu] _ /Zo_P [] /functionsP. 
  move => [fv srv tv] _ /functionsP [fs sss ts].
  have c1: u \coP fc by  split => //; ue.
  have c2: v \coP fc by  split => //; ue.
  move: (f_equal (fun z => z \co s) sv).
  by rewrite - !compfA // sd ts - {1} su (compf_id_r fu) - srv (compf_id_r fv).
move => y yf.
move /fp: yf => [] /Zo_P []/functionsP [fy sy ty] sjy fyv.
move /Zo_P: fc2 => [_ sj1].
have sysj: source y = source fc by ue.
have aux: forall x0 y0 : Set,
   inc x0 (source fc) ->
   inc y0 (source fc) -> Vf fc x0 = Vf fc y0 -> Vf y x0 = Vf y y0.
   rewrite sfc; move => a b aI bI; rewrite /fc ! LfV// => sv.
   move: (prb _ aI)(prb _ bI) => [s1 s2] [s3 s4].
   rewrite - sfa in s2 s4; move: (bij_inj bfa s2 s4 sv) => sf.
   move: s2; rewrite sfa - fyv; move /funI_P => [z zj] => ta.
   move: s1; rewrite ta => s1; rewrite - (iim_fun_set1_hi fy s1).
   by move: s3; rewrite - sf ta => s2; rewrite (iim_fun_set1_hi fy s2).
set h:= y \co s.
have pr1: fc \coP s by move:sc => [s1 s2].
have pr2: y \coP s by red;move: pr1 => [s1 s2 <-].
move:(sc) => [[_ s2 s3] s4].
have fh: function h by rewrite /h; fct_tac => //; rewrite sy - s3 sfc.
move: (f_equal source s4); aw; rewrite tfc => srs.
have hf: inc h  (functions J J). 
   by apply /functionsP; red; rewrite {2 3} /h; aw.
have sjh: surjection h.
  split => // y1; rewrite /h; aw => y1y; move: (proj2 sjy _ y1y).
  rewrite sy srs; move => [a ai ->].
  set b := Vf fc a; have bj: inc b J by rewrite - tfc /b; Wtac.
  have bs: inc b (source s) by ue.
  have bs3: inc (Vf s b) I by rewrite - sfc s3; Wtac.
  ex_tac; rewrite compfV//; apply: aux; rewrite ? sfc //. 
  move: (f_equal (Vf^~ b) s4);  rewrite compfV // idV //; ue.
have bh: bijection h.
   move /functionsP: hf => [_ sh th].
   apply: bijective_if_same_finite_c_surj; rewrite ? sh ? th=> //.
   by red; rewrite - cj; apply /NatP.
rewrite -(left_composable_value fy sj1 sysj aux sc (refl_equal h)). 
by exists h=> //;apply /Zo_P.
Qed.


Definition Bell_number n := cardinal (partitions (Nint n)).

Lemma Bell_pr E :
  finite_set E ->
  cardinal (partitions E) =
  csumb (Nintc (cardinal E)) (fun p => cardinal (partitionsx E p)).
Proof.
set n := cardinal E; move /NatP => nN.
suff h: (forall x, inc x (partitions E) -> inc (cardinal x) (Nintc n)).
  by rewrite (card_partition_induced h); apply:csumb_exten. 
move => x /Zo_P [] pa  [[pb pd] pc]; apply /(NintcP nN).
suff: injection (Lf rep x E) by move/inj_source_smaller; aw.
apply: lf_injective.
  by move => t tx; move: (rep_i (pc _ tx)) => h; rewrite - pb; union_tac.
move => u v ux vx sr; case: (pd _ _ ux vx) => // bad. 
empty_tac1 (rep u); first exact: (rep_i (pc _ ux)). 
rewrite sr;exact: (rep_i (pc _ vx)).
Qed.

Lemma Bell_pr1 n: natp n -> 
  Bell_number n = csumb (Nintc n) (nbpart n).
Proof.
move => nN. 
by rewrite /Bell_number (Bell_pr (finite_Nint n)) /nbpart (card_Nint nN). 
Qed.

Lemma Bell_pr2 E: finite_set E -> 
  cardinal (partitions E) = Bell_number (cardinal E). 
Proof.
move => fse; move/NatP: (fse) => nN.
rewrite (Bell_pr fse) (Bell_pr1 nN). 
by apply: csumb_exten  => p pn; rewrite nbpart_pr.
Qed.

Lemma Bell_rec n: natp n ->
  Bell_number (csucc n) = 
  csumb (Nintc n) (fun k => (binom n k) *c (Bell_number k)).
Proof.
move => nN.
set E := Nint (csucc n); set X := (partitions E).
set E' := (Nint n).
have nE: inc n E by apply: Nint_si.
have ce: cardinal E = csucc n by rewrite (card_Nint (NS_succ nN)).
have ce1: cardinal E' = n by rewrite (card_Nint nN).
have see': sub E' E  by apply:Nint_M. 
pose fb p :=  select (fun s => inc n s) p.
have prb: forall p, inc p X -> inc n (fb p) /\ inc (fb p) p.
  move => t  /Zo_P [_] [[pa pc] pb]; apply: (select_pr).
     move: nE; rewrite -pa; move /setU_P => [y sa sb]; ex_tac.
  move => x y xp nx yp ny; case: (pc _ _ xp yp) => // bad; empty_tac1 n.
have fcq: forall p, inc p X ->  cardinal (fb p -s1 n) <=c n.
  move => p pX; move: (prb _ pX) => [pa pb].
  move /Zo_P: pX => [] /setP_P h _. 
  move: (h _ pb) => /setP_P => /(sub_smaller); rewrite ce - (cpred_pr5 pa)=>w.
  case: (equal_or_not (cardinal (fb p)) \0c) => e1. 
    rewrite e1 cpred0; apply: (cle0n nN).
  apply/(cleSSP); fprops; first by apply:CS_pred;fprops.
  by rewrite - (proj2(cpred_pr (NS_le_nat w (NS_succ nN)) e1)).
pose fc p := n -c cardinal (fb p -s1 n).
have fcp: forall p, inc p X-> inc (fc p) (Nintc n).
  move => p pX; apply /(NintcP nN); apply:cdiff_le1; fprops.
rewrite /Bell_number (card_partition_induced fcp); apply: csumb_exten.
move => k /(NintcP nN) kn.
have kN:= (NS_le_nat kn nN).
rewrite (binom_symmetric nN kn).
rewrite -(card_p_subsets nN (NS_diff k nN) ce1).
set E1 := Zo _ _; set K1 := subsets_with_p_elements _ _.
pose phi := Lf (fun z => (fb z -s1 n)) E1 K1.
have pc: forall c, inc c E1 -> inc  (fb c -s1 n) K1.
  move => x /Zo_P [pa pb]; apply /Zo_P;split => //.
    apply /setP_P => t /setC1_P [pc pd]; apply /(NintP nN); split => //.
    move: (pa) => /Zo_S /setP_P sb; move /setP_P:(sb _ (proj2 (prb _ pa))).
    by move =>sc;  move /(NintsP nN): (sc _ pc).
  by rewrite -pb /fc double_diff //; apply: fcq.
have sphi: E1 = source phi by rewrite /phi; aw.
have tphi: K1 = target phi by rewrite /phi; aw.
have fphi: function phi by apply: lf_function. 
rewrite sphi tphi; apply: (shepherd_principle fphi).
rewrite - tphi => S /Zo_P [] /setP_P sa sb.
have ->: (Vfi1 phi S) =  Zo X (fun z => fb z -s1 n = S).
   set_extens t. 
      move /(iim_fun_set1_P _ fphi); rewrite - sphi; move => [s1].
      by rewrite /phi LfV// => s2; apply /Zo_P;split => //; move /Zo_P: s1 => [].
   move => /Zo_P [s1 s2]; apply /(iim_fun_set1_P _ fphi).
   have te1: inc t E1.
      by apply /Zo_P;split => //; rewrite /fc s2 sb double_diff.
   by rewrite - sphi /phi;split => //;rewrite LfV.
have sc: E -s (S +s1 n) = E' -s S.
     set_extens t.
       move => /setC_P [te] /setU1_P h; apply /setC_P.
       case: (equal_or_not t n) => tn; first by case: h; right.
       split; last by move => h1; case: h; left.
       by apply /(NintP nN); split => //; apply /(NintsP nN).
     move => /setC_P [t1 t2]; apply /setC_P; split; first by apply: see'.
     by apply /setU1_P; case => // tn; move /(NintP nN) : t1 => [].
have sd: k = n -c cardinal S by rewrite sb double_diff.
pose E'':= (E -s (S +s1 n)).
have se: cardinal E'' = k.
  have fse': finite_set E' by apply /NatP; rewrite (card_Nint nN).
  by rewrite /E'' sc (cardinal_setC4 sa fse') ce1 sd.
rewrite -/(Bell_number k) - se - Bell_pr2; last by apply/NatP; rewrite se.
symmetry; apply/ card_eqP.
set A:= partitions E''; set B := Zo _ _.
pose f p :=  p +s1 (S +s1 n).
have pa: forall p, inc p A -> inc (f p) (\Po (\Po E)).
  move => p /Zo_P [p1 [[p2 p4] p3]]; apply /setP_P => t /setU1_P; case.
    move => tp; apply /setP_P => s st.
    move/setP_P: p1 => h1; move: (h1 _ tp) => h2; move/setP_P: h2 => h3.
    by move: (h3 _ st) => /setC_P [].
  move => ->; apply /setP_P => s /setU1_P; case; fprops.
  move => ->; apply :(Nint_si nN).
have pb: forall p, inc p A -> inc (f p) X.
  move => p pA; move: (pa _ pA) => pn; apply /Zo_P; split => //.
  move /Zo_P: pA => [_] [[p1 p3] p2]; split; last first.
    move => t /setU1_P; case; [apply: p2 | move => ->; exists n; fprops].
    split; first set_extens t.
      move => /setU_P [z tz zf]; move/setP_P: pn => h; move: (h _ zf).
      by move /setP_P; apply.
    move => te; case: (inc_or_not t (S +s1 n)) => h.
      by union_tac; apply /setU1_P; right.
    move: (setC_i te h); rewrite -/E'' -p1 => /setU_P [z za zb].
    by union_tac; apply /setU1_P; left.
  move => a b /setU1_P; case => pb /setU1_P; case => pd.
      by apply: p3.
     right; rewrite pd; move: (setU_s1 pb); rewrite p1 => h.
     by apply: disjoint_pr => s sx; move: (h _ sx) => /setC_P [].
   right; rewrite pb; move: (setU_s1 pd); rewrite p1 => h.
    by apply: disjoint_pr => s sx sy; move: (h _ sy) => /setC_P [].
  by rewrite pb pd; left.
have pd: forall p, inc p A -> fb (f p) = (S +s1 n).
  move => p pA; move: (pb _ pA) => h; move: (prb _ h) => [s1 s2].
  case /setU1_P: s2 => // h1.
  move /Zo_P: pA => [] /setP_P ha _; move: (ha _ h1) => /setP_P => hb.
  by move: (hb _ s1) => /setC_P [_] /setU1_P; case; right.
exists (Lf f A B); saw;apply: lf_bijective.
    move => p pA; apply /Zo_P;split; first by apply: pb.
    rewrite (pd _ pA); apply: setU1_K => ns; move: (sa _ ns). 
    by move /(NintP nN) => [].
  move => u v uA vA sf.
   have aux: forall s, inc s A -> ~ inc (S +s1 n) s.
     move => s /Zo_P [] /setP_P h _ h1; move: (h _ h1) => /setP_P h2.
     have h3: inc n (S +s1 n) by fprops.
     by move: (h2 _ h3) => /setC_P [].
   by rewrite - (setU1_K (aux _ uA)) - (setU1_K (aux _ vA))  - /(f u) sf.
move => y /Zo_P [p1 p2]; move: (prb _ p1) => [p3 p4].
have aux: S +s1 n = fb y by  rewrite - p2;apply: setC1_K.
exists (y -s1 (fb y)); last  by symmetry;rewrite /f aux;apply: setC1_K.
have q1: inc (y -s1 fb y) (\Po (\Po E'')).
  apply /setP_P => t /setC1_P [] ta tb; apply /setP_P => s st; apply /setC_P.
  move /Zo_P: p1 => [] /setP_P ha [[q1 q3] q2]; split.
    by move: (ha _ ta) => /setP_P; apply.
  move => h; case: (q3 _ _ p4 ta); rewrite /disjoint => h1; first by case: tb.
  by empty_tac1 s; apply /setI2_P; split => //; rewrite - aux.
move /Zo_P: p1 => [_] [[q3 q5] q4].
apply /Zo_P;split => //; split; first split.
    move /setP_P: q1 => q2; set_extens t.
    by move /setU_P => [z za zb]; move: (q2 _ zb) => /setP_P; apply.
  move /setC_P => [t1 t2]; move: t1; rewrite -q3 => /setU_P [z z1 z2]. 
  by union_tac; apply /setC1_P;split => //; move => h; case: t2; rewrite aux -h.
by move => a b /setC1_P [s1 _] /setC1_P [s2 _]; apply: q5.
by move => s /setC1_P [sy _]; apply:q4.
Qed.


(* -- Exercise 8 *)

Definition derangements E :=
  Zo (permutations E) (fun z => forall x, inc x E -> Vf z x <> x).


Definition nbder n :=
  cardinal(derangements (Nint n)).

Lemma nbder_pr E: finite_set E -> 
   cardinal (derangements E) = nbder (cardinal E).
Proof.
have aux: forall I J g f, 
    bijection g -> source g = J -> target g = I ->
    inc f (derangements J) -> 
    inc  (g \co (f \co inverse_fun g)) (derangements I).
  move =>  I J g f big sg tg.
  move: (inverse_bij_fb big); set g1 := inverse_fun g => igb.
  move: (proj1 (proj1 big))(proj1(proj1 igb)) => fg fig.
  move => /Zo_P [] /Zo_P [] /functionsP [pa pb pc] pd pe.
  have qa: (f \coP g1) by rewrite /g1;red; saw; ue.
  have qb: bijection (f \co g1) by apply: compose_fb.
  have qc: (g \coP (f \co g1)) by  saw; try fct_tac; ue.
  have qd: bijection (g \co (f \co g1)) by apply: compose_fb.
  have sg1: source g1 = I by rewrite /g1; aw.
  have qe: inc (g \co (f \co g1)) (permutations I). 
     apply /Zo_P;split => //; apply /functionsP; saw;fct_tac.
  apply/ Zo_P; split => // => x xi /(f_equal (Vf g1)).
  rewrite - sg1 in xi;  bw; aw => //; rewrite -/g1; set y:= Vf g1 x.
  have ye: inc y J by rewrite- sg - ifun_t /y /g1; Wtac; aw.
  have ysg: inc (Vf f y) (source g) by rewrite sg - pc; Wtac.
  rewrite (inverse_V2 big ysg); exact (pe _ ye).
move => fse; set n := cardinal E; set I := Nint n.
have nN: natp n  by apply /NatP.
have : n = cardinal I by rewrite (card_Nint nN).
move/card_eqP => [g [big sg tg]]; apply /card_eqP.
pose c f := g \co (f \co (inverse_fun g)).
move: (inverse_bij_fb big); set g1 := inverse_fun g => igb.
move: (proj1 (proj1 big))(proj1(proj1 igb)) => fg fig.
exists (Lf c (derangements E) (derangements I)); saw.
apply: lf_bijective.
    by move => f;apply: aux.
  move => u v /Zo_P [] /Zo_P [] /functionsP [pa pb pc] _ _.
  move => /Zo_P [] /Zo_P [] /functionsP [qa qb qc] _ _ sv.
  have ra: (u \coP g1) by rewrite /g1;red; saw; ue.
  have rb: function (u \co g1) by fct_tac.
  have rc: (g \coP (u \co g1)) by saw; ue.
  have ra': (v \coP g1) by rewrite /g1;red; saw; ue.
  have rb': function (v \co g1) by fct_tac.
  have rc': (g \coP (v \co g1)) by  saw; ue.
  move: (fct_co_simpl_left rc rc' big sv) => sv1.
  exact: (fct_co_simpl_right ra ra' igb sv1).
move => y yv; set x :=  (g1 \co (y \co (inverse_fun g1))).
have sg1: source g1 = I by rewrite /g1; aw.
have tg1: target g1 = E by rewrite /g1; aw.
move: (aux _ _ _ _ igb sg1 tg1 yv); rewrite (ifun_involutive fg) => h; ex_tac.
move: yv => /Zo_P [] /Zo_P [] /functionsP [fy sy ty] _ _.
rewrite /c -/g1.
have pa: (y \coP g) by split => //; ue.
have pb: function  (y \co g) by fct_tac.
have pc: g1 \coP (y \co g) by saw; ue.
have pd: (y \co g) \coP g1 by saw; ue.
have pe: g1 \coP ((y \co g) \co g1) by red;aw;split => //; try fct_tac; ue.
move: (composable_f_inv big) => pf.
rewrite - compfA // compfA // bij_right_inverse //.
rewrite  - compfA // bij_right_inverse // tg - {2} sy compf_id_r //.
rewrite - ty compf_id_l //.
Qed.

Lemma nbder_0: nbder \0c = \1c.
Proof.
rewrite /nbder /derangements Nint_co00.
set X:= Zo _ _.
suff: X = singleton empty_function  by move => ->; rewrite cardinal_set1.
apply: set1_pr.
  apply/Zo_P; split; last by move => x /in_set0.
  apply/permutationsP; apply:empty_function_bf.
move => z /Zo_P [] /Zo_P [].
by rewrite functions_empty => /set1_P.
Qed.

Lemma nbder_1: nbder \1c = \0c.
Proof.
rewrite /nbder;set E := derangements _.
suff: E = emptyset by  move => ->; apply: cardinal_set0.
apply /set0_P => t /Zo_P  [] /Zo_P [] /functionsP [ff sf tf] _ pf.
move:Nint_co01 => [pa pb].
move: (pf _ pa) => f0.
by rewrite - sf in pa; move: (Vf_target ff pa); rewrite tf pb => /set1_P.
Qed.


Lemma nbdr_pr1 n:natp n ->
  factorial n = csumb (Nintc n) (fun k =>  binom n k *c nbder k).
Proof.
move => nN.
set I := (Nint n).
have caI : cardinal I = n by rewrite (card_Nint nN).
have fsi: finite_set I by apply: finite_Nint.
move: (card_permutations fsi); rewrite - caI => <-.
pose g f := Zo I (fun x => Vf f x <> x).
pose Xk k := Zo (permutations I) (fun z => cardinal (g z) = k).
set X := Lg (Nintc n) Xk.
have X1:  fgraph X by rewrite /X; fprops.
have X2:  mutually_disjoint X. 
  red;rewrite /X;aw => i j ip jp; rewrite ! LgV//;mdi_tac nij => u  ua ub; case: nij.
  by move: ua ub => /Zo_P [_ <- ]  /Zo_P [_ <-].
have X3: (unionb X) = (permutations I).
   rewrite /X;set_extens t.
     move /setUb_P; aw; move => [y yp]; rewrite LgV//; move /Zo_P => [p1 p2] //.
   have sa: inc (cardinal (g t)) (Nintc n).
     have h: sub (g t) I by apply: Zo_S.
     apply /NintcP => //; rewrite - caI; apply: (sub_smaller h).
   move => ti; apply /setUb_P; aw;exists (cardinal (g t)) => //.
   rewrite /Xk LgV// ;apply /Zo_P;split => //. 
move: (csum_pr4  X2); rewrite X3 => ->.
rewrite {1} /X /csumb caI; aw; apply: csumb_exten.
move => k kn; rewrite /X LgV//; move/(NintcP nN): kn => kn;clear X X1 X2 X3.
have kN:= (NS_le_nat kn nN).
rewrite - (card_p_subsets nN kN caI).
set K := (subsets_with_p_elements k I).
pose phi := Lf g (Xk k) K.
have sphi: (Xk k) = source phi by rewrite /phi; aw.
have ->: K = target phi by rewrite /phi; aw.
have ta: lf_axiom g (Xk k) K.
  by move => f /Zo_P [p1 p2]; apply/Zo_P;split => //; apply/setP_P; apply: Zo_S.
have fphi: function phi by apply: lf_function. 
rewrite sphi; apply: (shepherd_principle fphi).
rewrite {1} /phi; aw; move => x xK.
set W := (Vfi1 phi x).
have kp: forall f, inc f W <-> inc f (Xk k) /\ g f = x.
  move => f; split. 
    by move/(iim_fun_set1_P _ fphi); rewrite - sphi /phi; move => [h];rewrite LfV// => h1.   move => [pa pb]; apply/(iim_fun_set1_P _ fphi).
  have fsp: inc f (source phi) by rewrite - sphi.
  by rewrite /phi LfV.
move: (xK) => /Zo_P [] /setP_P sxi cx.
pose r f := Lf (Vf f) x x.
have pa: forall f, inc f W -> 
   [/\ lf_axiom (Vf f) x x,
     (forall t, inc t x -> Vf (r f) t = Vf f t),
    (forall t, inc t (I -s x) -> Vf f t = t) &
   inc (r f) (derangements x)].
  move => f /kp [] /Zo_P [] /Zo_P [] /functionsP [ff sf tf] bf fp gf.
  have lfa: lf_axiom (Vf f) x x.
     move => s st; move: (st); rewrite - gf => /Zo_P [si siv].
     have ax: inc (Vf f s) I by rewrite - tf; Wtac.
     apply /Zo_P;split => // => sv; rewrite - sf in si ax. 
     by move:(bij_inj bf ax si sv).
  have sv: forall t, inc t x -> Vf (r f) t = Vf f t.
     move => t tx; rewrite /r LfV//.
  have sv1:(forall t, inc t x -> Vf (r f) t <> t).
    by move => t tx; rewrite (sv _ tx); move: tx; rewrite - gf => /Zo_P [].
  have sv2: (forall t : Set, inc t (I -s x) -> Vf f t = t).
   by move => t /setC_P [ti tx];ex_middle fx;case: tx;rewrite - gf; apply /Zo_P.
  rewrite /r;split => //; apply /Zo_P;split => //.
  apply /Zo_P;split => //. 
    by  apply /functionsP;saw; apply:lf_function.
  apply: lf_bijective => //.
    by move => u v ux vx; apply: (bij_inj bf); rewrite sf; apply: sxi.
  move => y yx. 
  move: (sxi _ yx); rewrite -tf => ytf.
  move: (bij_surj bf ytf); rewrite sf; move => [z za zb]; exists z => //.
  by ex_middle zx; rewrite - (sv2 _ (setC_i za zx)) -zb.
have ->: nbder k = cardinal (derangements x).
   have fsx: finite_set x by apply /NatP; rewrite cx.
   by rewrite (nbder_pr fsx) cx.
apply /card_eqP; exists (Lf r W (derangements x)); saw.
apply:lf_bijective.
    by move => t ts; move: (pa _ ts) => [_ _ _].
  move => u v uw vw sr. 
  move: (pa _ uw) (pa _ vw) =>  [_ p1 p2 _] [_ q1 q2 _].
  move: uw  => /kp [] /Zo_P [] /Zo_P [] /functionsP [f1 f2 f3] _ _ _.
  move: vw => /kp [] /Zo_P [] /Zo_P [] /functionsP [f1' f2' f3'] _ _ _.
  apply: function_exten => //; try ue. 
  move => t ts; case: (inc_or_not t x) => tx.
    by rewrite - (p1 _ tx) - (q1 _ tx) sr.
  by rewrite f2 in ts; move : (setC_i ts tx) => h; rewrite (p2 _ h) (q2 _ h).
move => y yd.
move: yd => /Zo_P [] /Zo_P [] /functionsP [y1 y2 y3] y4 y5.
set f := Lf (fun z =>  (Yo (inc z x) (Vf y z) z)) I I.
have sa: forall z, inc z I -> inc ((Yo (inc z x) (Vf y z) z)) I.
  move => z zi; Ytac zx => //;apply: sxi; rewrite - y3; Wtac.
have ff: function f by apply: lf_function.
have gfx: g f = x.
   set_extens t. 
     by move /Zo_P => [t1 t2]; ex_middle ntx; case: t2; rewrite /f LfV//; Ytac0.
   move => tx; move: (sxi _ tx) => ti. 
   by apply /Zo_P;split => //;rewrite /f LfV//; Ytac0; apply: y5.
have bf: bijection f.
  apply: lf_bijective.
     move => s; apply: sa.
  move => u v ui vi; case: (inc_or_not u x) => ux; Ytac0.
       case: (inc_or_not v x) => vx; Ytac0.
         by apply (bij_inj y4); rewrite y2.
       rewrite -y2 in ux; move: (Vf_target y1 ux); rewrite y3.
       by move => s1 s2; case: vx; rewrite - s2.
    case: (inc_or_not v x) => vx; Ytac0 => //.
    rewrite -y2 in vx; move: (Vf_target y1 vx); rewrite y3.
    by move => s1 s2; case: ux; rewrite s2.
  move => z zi; case: (inc_or_not z x).
    rewrite - {1} y3 => zy; move: (bij_surj y4 zy) => [t ]; rewrite y2.
    by move => tx ->; move: (sxi _ tx) => ti; ex_tac; Ytac0.
   by move => zx; ex_tac; Ytac0.
have fp: inc f (permutations I) by rewrite/f;apply/permutationsP; saw.
have rfy: r f = y.
  symmetry;rewrite /r/f.
  have aux:
     lf_axiom (Vf (Lf (fun z0 => Yo (inc z0 x) (Vf y z0) z0) I I)) x x.
    move => t tx;move: (sxi _ tx) => ti; rewrite LfV//;Ytac0;rewrite - y3; Wtac.
  apply: function_exten; aw;trivial; first by apply lf_function => //. 
  by rewrite y2;move => s sx /=; move: (sxi _ sx) => si; rewrite !LfV//; Ytac0.
by exists f => //; apply /kp;split => //; apply /Zo_P;split => //; rewrite gfx.
Qed.

Lemma nbder_pr2 n: natp n -> 
   nbder (csucc (csucc n)) = (csucc n) *c (nbder n +c nbder (csucc n)).
Proof.
move => nN.
move: (NS_succ nN) => snN.
move: (Nint_pr4 snN).
set I :=Nint (csucc n); set I' := Nint (csucc (csucc n)).
move => [pa pb].
have pc: inc (csucc n) I' by apply:Nint_si.
have ci: cardinal I= csucc n by apply:(card_Nint snN).
set G1 := (derangements I').  
pose phi := Lf (Vf ^~(csucc n)) G1 I.
have sp: G1 = source phi by rewrite /phi; aw.
have tp: I = target phi  by rewrite /phi; aw.
have lfa: lf_axiom (Vf^~(csucc n)) G1 I. 
  move => f /Zo_P [] /Zo_P [] /functionsP [ta tb tc] td te.
  move: (te _ pc) => bad; move: pc; rewrite -tb => pc. 
  by move: (Vf_target ta pc); rewrite tc -pa; case /setU1_P. 
have fphi: function phi  by apply: lf_function.
have ci': cardinal I'= csucc (csucc n) by apply:(card_Nint (NS_succ snN)).
have <-: cardinal (source phi) = nbder (csucc (csucc n)).
    rewrite - sp - ci'; apply:nbder_pr; red; rewrite ci'; apply /NatP; fprops.
rewrite - {1} ci tp;apply:(shepherd_principle fphi).
rewrite {1} /phi; aw; move => x xK.
set G2 := Zo G1 (fun f => Vf f (csucc n) = x).
have ->: Vfi1 phi x = G2.
   set_extens t.
    move/(iim_fun_set1_P _ fphi); rewrite - sp;move => [ts].
      rewrite /phi /G2 LfV// => ->; apply /Zo_P;split => //.
  move => /Zo_P [tg1 <-]; apply /(iim_fun_set1_P _ fphi). rewrite /phi; aw; rewrite LfV//.
set G3 := Zo G2 (fun f => Vf f x = (csucc n)).
have sg3: sub G3 G2 by apply: Zo_S.
have h0: csucc n <> x by move => h1; case: pb; rewrite h1.
have fi: finite_set I' by apply: finite_Nint.
have xi': inc x I' by  rewrite - pa; fprops.
rewrite (cardinal_setC2 sg3) - csum2cl  - csum2cr; apply: f_equal2.
  set K := I -s1 x.
  have cK: n = cardinal K.
    by apply: csucc_inj; fprops; rewrite - ci (csucc_pr2 xK).
  have fsk: finite_set K by red; rewrite - cK; apply /NatP.
  rewrite cK - (nbder_pr fsk); apply /card_eqP.
  exists (Lf (fun f => (restriction2 f K K)) G3 (derangements K)). 
    saw.
  have ski': sub K I' by rewrite -pa;move => t /setC_P [ti _]; fprops.
  have pd: forall f, inc f G3 -> restriction2_axioms f K K.
     move => f /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [] /functionsP 
        [qa qb qc] qd qe qf qg.
     have ksf: sub K (source f) by ue.
     red; rewrite qb qc ;split => // t /(Vf_image_P qa ksf) [u uk ->].
     move: (ksf _ uk) => usf; move: (Vf_target qa usf); rewrite qc -pa.
     have xsf: inc x  (source f) by rewrite qb -pa; fprops.
     have nsf: inc (csucc n)  (source f) by rewrite qb -pa; fprops.
     move /setC1_P: uk => [ui ux]; case /setU1_P => h.
        apply /setC1_P;split => // => h1; rewrite -h1 in qf.
        by move: (bij_inj qd  nsf usf qf) => us; case: pb; rewrite us.
     by rewrite  -h in qg; move: (bij_inj qd xsf usf qg) => xu; case: ux.
  apply: lf_bijective.
      move => f fg3; move: (pd _ fg3) => pe. 
      set g := (restriction2 f K K).
      move: (restriction2_prop pe) => p0.
      have gs: inc g (functions K K) by apply /functionsP.
      move: p0 => [p1 p2 p3].
      move: fg3 => /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [] /functionsP 
        [qa qb qc] qd qe qf qg.
      move: (restriction2_fi (proj1 qd) pe) => ir.
      apply /Zo_P; split; first (apply/Zo_P => //; split => //).
        apply:bijective_if_same_finite_c_inj; rewrite ? p2 ? p3 //.
      move => t tK; rewrite  (restriction2_V pe tK); apply: qe; fprops.
    move => u v ug3 vg3; move: (pd _ ug3) (pd _ vg3) => pe pe' sr.
    move: ug3 => /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [] /functionsP 
      [qa qb qc] qd qe qf qg.
    move: vg3 => /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [] /functionsP 
      [qa' qb' qc'] qd' qe' qf' qg'.
    apply: function_exten; rewrite ? qb' ? qc' //.
    rewrite qb -pa => t; case /setU1_P ; last by move => ->; rewrite qf.
    move => ti; case: (equal_or_not t x); first by move => ->; rewrite qg.
    move => tx; move /setC1_P: (conj ti tx) => tK.
    by rewrite - (restriction2_V pe tK) - (restriction2_V pe' tK) sr.
  move => y ydK.
  move: ydK => /Zo_P [] /Zo_P [] /functionsP [fy sy ty] biy nfy.
  pose f z := Yo (z = csucc n) x (Yo (z = x) (csucc n) (Vf y z)).
  have f1: f (csucc n) = x by  rewrite /f; Ytac0; Ytac0.
  have f2: f x = (csucc n) by rewrite /f; Ytac0; Ytac0.  
  have f3: forall t, inc t K -> f t = Vf y t.
  move => t /setC1_P [ti tk]; rewrite /f; Ytac0; Ytac h => //; case: pb; ue.
  have f4: forall t, inc t K -> inc (f t) K.
       move => t tk; rewrite (f3 _ tk); rewrite - ty; Wtac.
  have f5: lf_axiom f I' I'.
      move => t; rewrite -pa; case: (equal_or_not t x). 
        by move ->; rewrite f2; fprops.
      move => tx; case/setU1_P => ta; last by rewrite ta f1; fprops.
      by rewrite pa; apply: ski'; apply: f4;apply /setC1_P.
    have f6: function  (Lf f I' I') by apply:lf_function.
    have f7: restriction2_axioms (Lf f I' I') K K.
       have h: sub K (source (Lf f I' I')) by aw.
       red; aw;split => // t; move /(Vf_image_P f6 h) => [u uK]. 
       by rewrite LfV//; fprops => ->; apply: f4.
    move: (restriction2_prop f7) => [p1 p2 p3].
    have f8: (restriction2 (Lf f I' I') K K) = y.
       apply: function_exten; rewrite ? p2 ? p3 //.
       move => t tk /=; rewrite (restriction2_V f7) // LfV//; fprops.
    have f9: forall t, inc t I' -> f t <> t.
      move => t; rewrite -pa; case: (equal_or_not t x).
        move => -> _; rewrite f2 //. 
      move => tx; case /setU1_P; last  by move => ->; rewrite f1; fprops.
      move => ti; move /setC1_P: (conj ti tx) => tK. 
      by rewrite (f3 _  tK);apply: nfy.
   have f10: inc (Lf f I' I') (permutations I').
     apply /Zo_P; split; first by apply /functionsP; red;saw.
     apply:bijective_if_same_finite_c_surj; aw; trivial. 
     apply /lf_surjective => //.
     move => z; rewrite - pa; case /setU1_P; last first.
       move => ->; exists x;fprops.
     case: (equal_or_not z x)=> zx zi.
         by rewrite zx; exists (csucc n); fprops.
     move /setC1_P: (conj zi zx); rewrite -/K - ty => yt.
     move: (bij_surj biy  yt) => [w]; rewrite sy => wK ->.
     by rewrite - (f3 _ wK); exists w=> //; rewrite pa; apply: ski'.  
  exists (Lf f I' I')=> //; apply /Zo_P; rewrite LfV// ; split => //. 
  apply /Zo_P; rewrite ! LfV//;split => //.
  by apply /Zo_P;split => // => t ti; rewrite LfV//; apply: f9.
set G4 := Zo G2 (fun f => Vf f x <> csucc n).
have ->:  (G2 -s G3) = G4.
  set_extens t.
    by move /setC_P => [tg2] /Zo_P p3; apply /Zo_P;split => // h; case: p3.
  by move => /Zo_P [p1 p2]; apply /setC_P;split => // ; move => /Zo_P [q1 q2].
pose g f := fun z => Yo (z = Vf (inverse_fun f) (csucc n)) x (Vf f z).
pose g1 f := Lf (g f) I I.
have pd: forall f (y:=  Vf  (inverse_fun f) (csucc n)), inc f G4 -> 
      [/\ Vf f y = csucc n, inc y I,  (g f y) = x,
      (forall t, t <> y -> (g f t) = Vf f t) &
      (forall z, inc z I -> inc (g f z) I)].
  move => f y /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [].
  move /functionsP => [ff sg tf] bf nfp fn fx.
  move:(inverse_bij_fb bf) => ifb.
  have stf: inc (csucc n) (target f)  by rewrite tf -pa; fprops.
  have ysf: inc y (source f).
     by move: (Vf_target (proj1 (proj1 ifb))); aw; apply.
  have f1: Vf f y = csucc n by rewrite /y inverse_V //. 
  have yI: inc y I. 
     rewrite sg in ysf; move: (nfp _ ysf) => yy.
     by move: ysf; rewrite -pa; case /setU1_P => // ysn; case: yy; rewrite f1.
  have f2: x <> y by  dneg w; ue.
  have f3: (g f y) = x by rewrite /g /y; Ytac0.
  have f4: forall t, t <> y -> (g f t) = Vf f t. 
    by move => t; rewrite  /y /g => ty; Ytac0.
  have f5: (forall z, inc z I -> inc (g f z) I).
    move => z zI; case: (equal_or_not z y); first by move => ->; rewrite f3.
    move => zy; rewrite (f4 _ zy).
    have zsi: inc z (source f) by rewrite  sg -pa; fprops.
    move: (Vf_target ff zsi); rewrite tf - pa; case /setU1_P => //.
    by move => h; rewrite -h in f1; case: zy; rewrite (bij_inj bf ysf zsi f1).
  done.
have fsi: finite_set I by red; rewrite ci; apply /NatP.
move: (nbder_pr fsi); rewrite ci => <-.
apply /card_eqP; exists (Lf g1 G4 (derangements I)).
saw; apply: lf_bijective.
    move => f fg4; move: (pd _ fg4).
    set y := (Vf (inverse_fun f) (csucc n)); move=> [f1 yI f3 f4 f5].
    move: fg4 => /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [].
    move /functionsP => [ff sg tf] bf nfp fn fx.
    have f2: x <> y by  dneg w; ue.
    have f6: function (g1 f) by apply /lf_function.
    have f7: bijection (g1 f).
      rewrite /g1.
      apply:bijective_if_same_finite_c_surj; aw; trivial.
      apply /lf_surjective => //.
      move => t tI; have ti': inc t (target f) by rewrite tf -pa; fprops.
      move: (bij_surj bf ti'); rewrite sg; move => [u ui uv].
      rewrite -pa in ui;case /setU1_P: ui; last first.
      move => h; exists y => //; rewrite f3 uv h fn => //.
      by move => ui; ex_tac; rewrite f4 // => uy; case: pb; rewrite -f1 - uy -uv.
    have f8: inc (g1 f) (permutations I).
      by apply /Zo_P;split => //; rewrite /g1;apply /functionsP;red;aw.
    apply /Zo_P; split => // t ti;  case: (equal_or_not t y).
      by move => ty; rewrite /g1 LfV// ty f3.
    move => ty; rewrite /g1 LfV//; rewrite (f4 _ ty). 
    apply: nfp; rewrite -pa; fprops.
  move => u v ug4 vg4 sg1.
  move: (ug4) => /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [].
  move /functionsP => [ff sg tf] bf nfp fn fx.
  move: (vg4) => /Zo_P [] /Zo_P [] /Zo_P [] /Zo_P [].
  move /functionsP => [ff' sg' tf'] bf' nfp' fn' fx'.
  apply: function_exten; rewrite ? sg ?sg' ? tf' //.
  move => t; rewrite - pa; case /setU1_P; last by move => ->; rewrite fn fn'.
  move => tI.
  move: (pd _ ug4) (pd _ vg4).
  set y := (Vf (inverse_fun u)  (csucc n)); move=> [f1 yI f3 f4 f5].
  set y' := (Vf  (inverse_fun v) (csucc n)); move=> [f1' yI' f3' f4' f5'].
  move: (f_equal (fun z => Vf z t) sg1); rewrite /g1 ! LfV//.
  have tsn: t <> csucc n by move => h; case: pb; rewrite -h.
  have i1: Vf v (csucc n)  <> Vf v t.
    have tsv: inc t (source v) by rewrite sg' -  pa; fprops.
    have nsv: inc (csucc n) (source v) by rewrite sg' -  pa; fprops.
    by move => h; case: tsn; rewrite (bij_inj bf' nsv tsv h).
  have i2: Vf u (csucc n)  <> Vf u t.
    have tsv: inc t (source u) by rewrite sg -  pa; fprops.
    have nsv: inc (csucc n) (source u) by rewrite sg -  pa; fprops.
    by move => h; case: tsn; rewrite (bij_inj bf nsv tsv h).
  case: (equal_or_not t y) => ty.
     rewrite {1 3} ty f3 f1.
    case: (equal_or_not t y'); first by move => ->; rewrite f1'.
    by move => ty'; rewrite (f4' _ ty') - fn'.
  rewrite (f4 _ ty); case: (equal_or_not t y') => ty'; last by rewrite f4'.
  rewrite ty'  f3' f1' -  fn - ty' => h; by case: i2.
move => y /Zo_P [] /Zo_P [] /functionsP [fy sy ty] biy dy.
set xx := Vf (inverse_fun y) x.
 move:(inverse_bij_fb biy) => iyb.
have xty: inc x (target y) by ue.
have xxsf: inc xx (source y).
  by move: (Vf_target (proj1 (proj1 iyb))); aw; rewrite  ty; apply.
have xxns: xx <> csucc n by move => h; case: pb; rewrite -h - sy.
have f1: Vf y xx = x by rewrite /xx inverse_V //.
pose f z := Yo (z = csucc n) x (Yo (z = xx) (csucc n) (Vf y z)).
have f2: f (csucc n) = x by rewrite /f; Ytac0; Ytac0.
have f3: f xx = (csucc n) by rewrite /f; Ytac0; Ytac0.
have f4: forall t, t <> csucc n -> t <> xx -> f t = Vf y t.
  by move => t t1 t2; rewrite /f; Ytac0; Ytac0.
have f5: f x <> csucc n.
  rewrite /f; Ytac0; Ytac xa; first by case: (dy _ xK); rewrite xa f1.
  move => h; case: pb; rewrite -h - ty; Wtac.
have f6: forall t, inc t I' -> inc (f t) I'.
   move => t; rewrite -pa => ti; case: (equal_or_not t (csucc n)) => tn.
      rewrite  tn f2; fprops.
   case: (equal_or_not t xx) => txx.
      rewrite txx f3; fprops.
   rewrite (f4 _  tn txx); apply /setU1_P; left.
   rewrite -ty; Wtac; rewrite sy; case /setU1_P: ti => //.
have f7: function (Lf f I' I') by apply /lf_function.
have f8: bijection (Lf f I' I').
   apply:bijective_if_same_finite_c_surj; aw; trivial.
   apply /lf_surjective => //.
   move => t; rewrite -pa => /setU1_P; case; last first.
     move => ->; exists xx=> //; rewrite - sy;fprops.
   rewrite - ty => tty; move: (bij_surj biy tty) => [a asy av].
   have asn: a <> csucc n by move => h; case: pb; rewrite -h - sy.
   case: (equal_or_not a xx); last first.
      by move =>axx; rewrite ty - sy; exists a;fprops; rewrite av f4. 
   by move => ax; exists (csucc n); fprops;rewrite f2 av ax f1. 
have f9: inc  (Lf f I' I') G1.
  apply /Zo_P; split.
    by apply /Zo_P;split => //;apply /functionsP;red; aw.
  move => t ti;rewrite LfV //;  
  case: (equal_or_not t (csucc n)) => tn; first by rewrite tn f2; fprops.
  case: (equal_or_not t xx) => tx; first by rewrite tx f3; fprops.
  by rewrite (f4 _ tn tx); apply: dy; move: ti; rewrite -pa; case /setU1_P.
have f10: inc  (Lf f I' I') G4 by apply:Zo_i;try apply:Zo_i => //; rewrite LfV.
have II: sub I I' by rewrite -pa => t ti; fprops.
have f11: Vf (inverse_fun (Lf f I' I')) (csucc n)  = xx.
  have xxI': inc xx I' by apply: II; rewrite - sy.
  have ->: csucc n = Vf (Lf f I' I') xx by  rewrite LfV.
  by rewrite inverse_V2 //; aw.
have f12: lf_axiom (g (Lf f I' I')) I I.
  move => t ti; move: (II _ ti) => ti'; rewrite /g LfV// f11.
  Ytac aux; fprops; rewrite - ty; rewrite (f4 _ _ aux); try Wtac.
  by move => tn; case: pb; rewrite -tn.
have f13: function (Lf (g (Lf f I' I')) I I) by apply: lf_function.
ex_tac; rewrite /g1; apply: function_exten; aw;trivial.
rewrite sy => t ti;  move: (II _ ti) => ti';rewrite /g LfV//.
rewrite f11; Ytac aa ; rewrite ? aa // LfV//  f4//.
by move => tn; case: pb; rewrite -tn.
Qed.

Lemma nbder_pr3 f (g := fun n => (csucc n) *c (f n)):
  (f \0c = \1c) -> f \1c = \0c ->
  (forall n, natp n -> 
    f (csucc (csucc n)) = (csucc n) *c (f n +c  f (csucc n))) ->
  (forall n, natp n -> (evenp n) -> f n <> \0c)
  /\
  (forall n, natp n -> 
     f (csucc n) = Yo (evenp n) (cpred (g n)) (csucc (g n))).
Proof.
move => pa pb pc. 
move: succ_zero => s0.
have pd': forall n, natp n -> natp (f n) /\ natp (f (csucc n)).
  apply: Nat_induction; first by rewrite s0 pa pb;split;fprops.
  move => n nB [hr1 hr2]; split => //; rewrite(pc _ nB); fprops.
have pd: (forall n, natp n -> natp (f n)).
  move => n nN; exact (proj1 (pd' _ nN)).
have pe: (forall n, natp n ->  f (csucc (csucc n)) <> \0c).
  apply: Nat_induction.
     rewrite (pc _ NS0) s0 pa pb (csum0r CS1) (cprod1r CS1); fprops.
  move => n nN h; move: (NS_succ nN) => h1; rewrite (pc _ h1).  
  move: (cpred_pr (pd _ (NS_succ h1)) h) => [pg ->].
  rewrite  (csum_nS _ pg);apply: cprod2_nz; apply: succ_nz.
have pf: (forall n, natp n -> evenp n -> f n <> \0c).
  move => n nN en; case: (equal_or_not n \0c).
    move => ->; rewrite pa; fprops.
  move => nz; move: (cpred_pr nN nz) => []; set p := (cpred n) => q1 q2.
  case: (equal_or_not p \0c) => pz. 
    by case: odd_one => [] _; rewrite - succ_zero - pz - q2.
  move: (cpred_pr q1 pz) => [pp]; rewrite q2 => ->; fprops.
split; first by exact.
apply: Nat_induction.
  move: even_zero => h; Ytac0; rewrite /g pa s0 pb -(cpred_pr2 NS0) s0.
  by rewrite (cprod1r CS1).
move => n nN Hrec.
have snN:= NS_succ nN.
rewrite (pc _ nN) cprodDr.
set sn := csucc n.
have sa: sn +c \1c =  csucc sn by rewrite Nsucc_rw.
have ->:  Yo (evenp sn) (cpred (g sn)) (csucc (g sn)) =
   (Yo (evenp sn) (cpred (f sn)) (csucc (f sn))) 
   +c  (sn *c f sn).
   rewrite /g - sa  cprodDl csumC (cprod1l (CS_nat (pd _ snN))).
   Ytac ok; Ytac0; last by  rewrite (csum_Sn _  (pd _ snN)) //.
   case: (equal_or_not (f sn) \0c) => tz.
     by rewrite tz cprod0r (Nsum0r NS0) cpred0 (Nsum0r NS0).
   move: (cpred_pr  (pd _ snN) tz) => [ta tb].
   rewrite {1} tb csum_Sn // cpred_pr1 //; fprops.
congr (_ +c (sn *c f sn)).
rewrite Hrec /g -/sn.
case: (p_or_not_p (evenp n)) => en.
  move: (proj2 (succ_of_even en)) => nesn; Ytac0; Ytac0. 
  have gnz := (cprod2_nz (@succ_nz n) (pf _ nN en)).
  by move: (cpred_pr (NS_prod snN (pd _ nN)) gnz)=> [_].
move: (succ_of_odd (conj nN en)) => nesn; Ytac0; Ytac0. 
rewrite cpred_pr1; fprops.
Qed.

Lemma nbder_pr4 n  (g := fun n => (csucc n) *c (nbder n)):
 natp n -> nbder (csucc n) = Yo (evenp n) (cpred (g n)) (csucc (g n)).
Proof.
apply:(proj2 (nbder_pr3 (f:= nbder) nbder_0 nbder_1 nbder_pr2)).
Qed.

(** Exercise 5.9 *)


Definition partition_nq E q:= 
  Zo (partitions E) (fun z => forall x, inc x z ->  cardinal x = q).

Lemma partition_nq_pr1 E q p:
 inc p (partition_nq E q) -> cardinal E = q *c (cardinal p).
Proof.
move => /Zo_P [/Zo_P[ ha [[hb1 hb2] hb3]] hc].
have hd:mutually_disjoint (identity_g p).
  by hnf;rewrite identity_d =>  i j ip jp; rewrite !identity_ev //; apply: hb2.
rewrite - hb1 - setUb_identity (csum_pr4 hd) identity_d.
rewrite cprod2cr - csum_of_same; apply: csumb_exten => a ap.
by rewrite (identity_ev ap); apply: hc.
Qed.

Lemma partition_nq_pr2 E q n p : cardinalp n -> natp q -> q <> \0c ->
  cardinal E = q *c n ->
  inc p (partition_nq E q) -> cardinal p = n.
Proof.
move => cn qN qnz ha hb.
move: (partition_nq_pr1 hb); rewrite ha => hc.
by move:(cprod_eq2lx qN cn (CS_cardinal p) qnz hc).
Qed.

Lemma partition_nq_pr3 E: E = emptyset \/ partition_nq E \0c = emptyset.
Proof.
case: (emptyset_dichot (partition_nq E \0c))=> h; [by right | left ].
by move: h => [p /partition_nq_pr1]; rewrite cprod0l; apply:card_nonempty.
Qed.

Lemma partition_nq_pr4 E: 
  cardinal (partition_nq E \0c) = Yo (E = emptyset) \1c \0c.
Proof.
case: (equal_or_not E emptyset) => ee; Ytac0;last first.
  by case:(partition_nq_pr3 E) => // ->; rewrite cardinal_set0.
have ha: inc emptyset (partition_nq E \0c).
  apply:Zo_i; last by move => p /in_set0.
  apply:Zo_i; [ apply:setP_0i | split; first split ].
  - by rewrite setU_0 ee. 
  - by move => a b /in_set0.
  - by move => a /in_set0.
have hb: forall z, inc z (partition_nq E \0c) -> z = emptyset.
  move => z /Zo_P [/Zo_P [ra [rb rc]] rd].
  move: ra; rewrite ee setP_0 setP_1 => /set2_P; case => // zz.
  have: inc emptyset z by rewrite zz; fprops.
  by move/rc => /nonemptyP. 
by rewrite (set1_pr ha hb) cardinal_set1.
Qed.

Definition Ex59_num q n := (factorial (q *c n)). 
Definition Ex59_den q n:= (factorial n) *c (factorial q) ^c n. 
Definition Ex59_val q n:= (Ex59_num q n) %/c (Ex59_den q n). 

Lemma partition_nq_pr5 E: 
  (partition_nq E \1c) = singleton (greatest_partition E).
Proof.
set p := greatest_partition E.
have ha: inc p  (partition_nq E \1c).
  apply /Zo_P; split; first apply: Zo_i.
  - by apply/setP_P => t /funI_P [z zE ->]; apply/setP_P => x /set1_P ->.
  - exact:greatest_is_partition.
  - by move => x /funI_P [z zE ->]; rewrite cardinal_set1.
apply: (set1_pr ha) => z /Zo_P [/Zo_P [/setP_P hc [[hb _] _]] hd].
set_extens t.
  move => tz; apply/funI_P.
  move/set_of_card_oneP :(hd _ tz) => [x tx]; exists x => //.
  move /setP_P: (hc _ tz); apply; rewrite tx; fprops.
move => /funI_P [x xE ->].
move: xE; rewrite - hb => /setU_P [y xy yz].
move/set_of_card_oneP :(hd _ yz) => [x' tx'].
by rewrite tx' in xy; rewrite (set1_eq xy) - tx'.
Qed.

Lemma partition_nq_pr5b E:  cardinal (partition_nq E \1c) = \1c.
Proof. by rewrite partition_nq_pr5 cardinal_set1. Qed.

Lemma partition_nq_pr5c E: finite_set E ->
  cardinal (partition_nq E \1c) = Ex59_val \1c (cardinal E). 
Proof. 
move => /NatP nN; rewrite /Ex59_val/Ex59_num/Ex59_den.
have fN:=(NS_factorial nN).
rewrite partition_nq_pr5b factorial1 cpow1x (cprod1l (CS_nat nN)).  
by rewrite (cprod1r (CS_nat fN)) (cquo_itself fN (factorial_nz nN)).
Qed.

Lemma partition_nq_pr6c E E' q g:  bijection_prop g E E' ->
   lf_axiom (extension_p3 g) (partition_nq E q) (partition_nq E' q).
Proof.
move => bg z /Zo_P [za zb]; apply:(Zo_i (ext2_pr8 bg za)).
move:za => /Zo_P [ zz zc].
move => x /(ext2_pr3 bg zz) [u uz ->].
move:(bg) => [[ig _] sg _].
have usg: sub u (source g) by rewrite sg;apply/setP_P; move/setP_P:zz; apply.
rewrite (cardinal_image usg ig); exact: (zb _ uz).
Qed.

Lemma partition_nq_pr6d E E' q:  E \Eq E' ->
  (partition_nq E q) \Eq (partition_nq E' q).
Proof.
move => [g gp].
exists (Lf (extension_p3 g) (partition_nq E q) (partition_nq E' q)).
hnf; aw; split => //; apply: lf_bijective.
- by apply: partition_nq_pr6c.
- move => u v /Zo_S /Zo_S ua  /Zo_S /Zo_S  va sv. 
  by rewrite  -(ext2_pr7 gp ua) -(ext2_pr7 gp va) sv.
- move => y yp; move: (yp) => /Zo_S /Zo_S ypp.
  move: (gp) => [ha1 ha2 ha3].
  move: (ext2_pr7 (inverse_bij_bp gp) ypp) 
      (partition_nq_pr6c (inverse_bij_bp gp) yp). 
  rewrite (ifun_involutive (proj1 (proj1 ha1))) =>{2}  <- h; ex_tac.
Qed.

Lemma partition_nq_pr7 E n q: \0c <c q -> cardinal E = q *c n ->
  nonempty (partition_nq E q).
Proof.
have H: forall A B, B \Eq A -> nonempty A -> nonempty B.
  move => A B /card_eqP ca /nonemptyP /card_nonempty0 cb. 
  by case: (emptyset_dichot B)=> // bE; case: cb; rewrite - ca bE cardinal_set0.
move=> qp eq1; move:(proj32_1 qp) => cq.
have e1: E \Eq q \times n by apply/card_eqP; rewrite eq1 - cprod2_pr1.
apply: (H _ _ (partition_nq_pr6d q e1)); clear H eq1 e1.
set X := fun_image n (indexed q).
have ra: forall x, inc x X -> cardinal x = q.
  by move => x /funI_P [i _ ->]; rewrite cardinal_indexed (card_card cq).
have rb:inc X (\Po (\Po (q \times n))).
  apply/setP_P => t/funI_P [z zn ->].
  apply/setP_P => s /setX_P [ha hb /set1_P hc]. 
  by apply/setX_P; split => //;rewrite hc. 
have rc:alls X nonempty.  
  move=> x /ra cx; apply/nonemptyP => xe.
  by case: (proj2 qp); rewrite - cx xe cardinal_set0.
have rd:union X = q \times n.
  set_extens t.  
    move /setU_P => [y ty yx]; move/setP_P: rb=> xa. 
    by move/setP_P:(xa _ yx); apply.
  move => /setX_P [pa pb pc]; apply/setU_P; exists (indexed q (Q t)).
    apply/setX_P; split => //; fprops.
  apply/funI_P; ex_tac.
have he:disjoint_set X.
  move => a b /funI_P [a' _ ->] /funI_P [b' _ ->].
  by apply:disjoint_pr1 => x /setX_P [_ _ /set1_P <-] /setX_P [_ _ /set1_P <-].
exists X; apply:Zo_i => //; apply: Zo_i => //.
Qed.

Lemma partition_nq_pr8 E q x y: natp q -> q <> \0c ->
  inc x (partition_nq E q) -> inc y (partition_nq E q) ->
  exists2 f, inc f (permutations E)  &  
     Vfs (extension_to_parts f) x = y.
Proof.
move => qN qp xp yp.
move:(partition_nq_pr1 yp) => ha.
move:(partition_nq_pr2 (CS_cardinal y) qN qp ha xp) => /card_eqP [f [bf sf tf]].
move:(xp) => /Zo_P [/Zo_P [_ [/partition_same ra]]] _ _.
move:xp => /Zo_P [ /Zo_P [pa [[pb pc] pd]] pe].
move:yp => /Zo_P [ /Zo_P [qa [[qb qc] qd]] qe].
pose h1 i := equipotent_ex i  (Vf f i).
have ff: function f by fct_tac.
have h1p: forall i, inc i x -> bijection_prop (h1 i) i (Vf f i).
   move => i ix; apply:equipotent_ex_pr.
   apply/card_eqP; rewrite (pe _ ix) qe //; Wtac. 
pose h i:= Lf (Vf (h1 i)) i E.
have rb': forall i j, inc i x -> inc j i ->  inc (Vf (h1 i) j) E.
  move => i j ix ij; move:(h1p _ ix) => [[[fa _] _] sa ta].
  rewrite - qb; apply /setU_P; exists (Vf f i); Wtac; fct_tac.
have rb: (forall i, inc i (domain (identity_g x)) ->
   function_prop (h i) (Vg (identity_g x)  i) E). 
  rewrite identity_d => i ix; rewrite (identity_ev ix) /h; hnf;aw.
  by split => //; apply:lf_function => j ji; apply: rb'.
move:(extension_partition1 ra rb); set g:= common_ext _ _ _.
move => [[fg sg tg] rc].
have rc': forall i, inc i  x -> agrees_on i g (h i).
  by move => i ix;move: (rc i); rewrite identity_d (identity_ev ix); apply.
have rc'': forall i j, inc i x -> inc j i -> Vf g j = Vf (h1 i) j.
  move => i j ix ij; move: (rc' _ ix) => [sa sb sc]; rewrite (sc j ij).
  by rewrite /h LfV//; move => t ti; apply: rb'.
have rd: injection g.
  split => //; rewrite sg -pb => u v /setU_P [xa uxa xax] /setU_P [xb vxb xbx].
  rewrite (rc'' _ _ xax uxa) (rc'' _ _ xbx vxb) => eq1.
  have sa: inc (Vf (h1 xa) u) (Vf f xa).
     move:(h1p _ xax) => [[[fa _] _] sa sb]; Wtac.
  have sb: inc (Vf (h1 xb) v) (Vf f xb).
     move:(h1p _ xbx) => [[[fa _] _] sa' ta]; Wtac.
  have sc: inc (Vf f xa) y by Wtac.
  have sd: inc (Vf f xb) y by Wtac.
  case:(qc _ _ sc sd)=> ea; last by  empty_tac1 (Vf (h1 xa) u); rewrite eq1. 
  move: (proj2 (proj1 bf)); rewrite sf => iif; move: (iif _ _ xax xbx ea) => eb.
  rewrite eb in eq1 uxa.
  move:(h1p _ xbx)=> [[[_ se] _] sh th]; apply:se;rewrite ? sh //.
have re: surjection g.
  split => //; rewrite sg tg - {1} qb => t /setU_P [s ts sy].
  rewrite - tf in sy; move: (proj2 (proj2 bf) _ sy) => [u usf sv].
  rewrite sf in usf.
  move:(h1p _ usf) => [[_ [_ ssa]] sa ta].
  have: inc t (target (h1 u)) by rewrite ta - sv.
  move/ssa; rewrite sa; move => [w wu ->]; exists w.
     rewrite - pb; union_tac.
  by rewrite (rc'' _ _ usf wu).
have bpg: bijection_prop g E E by [].
have rf: inc g (permutations E) by apply/permutationsP.
ex_tac. 
have ti: forall u, inc u x -> Vfs g u = Vf f u.
  move => u ux; move:(h1p _ ux) => [[ba [fh sh]] sa <-].
  have su: sub u (source g) by rewrite sg; apply/setP_P; move/setP_P:pa; apply.
  set_extens t.
     move /(Vf_image_P fg su) => [v uv ->]; rewrite (rc'' _ _ ux uv); Wtac.
  move/sh; rewrite sa;move => [v vx ->]; apply/(Vf_image_P fg su).
  by ex_tac; rewrite (rc'' _ _ ux vx).
set_extens t.
   move/(ext2_pr3 bpg pa) => [u ux ->]. rewrite (ti _ ux) - tf; Wtac.
rewrite -tf; move/(proj2 (proj2 bf)); rewrite sf; move => [u ux ->].
by apply/(ext2_pr3 bpg pa); ex_tac; rewrite - (ti _ ux). 

Qed.

Lemma partition_nq_pr9 E q n:
  natp n -> natp q -> \0c <c q -> cardinal E = q *c n -> 
  cardinal (partition_nq E q) *c (Ex59_den q n) = (Ex59_num q n) .
Proof.
move => nN qN qp cardE.
move:(partition_nq_pr7 qp cardE) => [p0 p0p].
move /Zo_P: (p0p) => [/Zo_P [/setP_P ha [[hb hc] hd]] he].
pose F f:= extension_p3 f p0.
have Ha: forall f, inc f (permutations E) -> inc (F f) (partition_nq E q).
  by move => f/permutationsP fp; apply: (partition_nq_pr6c fp p0p).
set F0 := Lf F (permutations E) (partition_nq E q).
have fF0: function F0 by apply: lf_function.
have <-: cardinal (source F0) = Ex59_num q n.  
  rewrite /F0 lf_source (card_permutations) ?cardE //. 
  apply/NatP; rewrite cardE; fprops.
suff kk: forall x, inc x (target F0) -> 
   cardinal (Vfi1 F0 x) = Ex59_den q n.
  by rewrite (shepherd_principle fF0 kk) lf_target.
rewrite lf_target => x xp.
have px:inc p0 (\Po (\Po E)) by apply /setP_P.
rewrite (iim_fun_set1_E _ fF0) lf_source.
move: (partition_nq_pr8 qN (nesym (proj2 qp)) p0p xp) => [sig sigp <-].
set T := Zo _ _.
have ->: T = Zo (permutations E) (fun f => F ((inverse_fun sig) \co f) = p0).
  apply: Zo_exten1 => t tE;rewrite /F0 LfV//.
  move/permutationsP: tE => pa.
  move/permutationsP: sigp => pb; move :(inverse_bij_bp pb) => pc.
  rewrite /F - (ext2_pr6 pa pc px); split => sa.
    by rewrite - sa (ext2_pr7 pb px).
  rewrite - (ext2_pr7 pc (ext2_pr5 pa px)).
  rewrite -{1} sa  - {1} (ifun_involutive (proj1 (proj1 (proj31 pb)))) //.
transitivity  (cardinal (Zo (permutations E) (fun f  => F f = p0))).
  apply/card_eqP; set A := Zo _ _; set B := Zo _ _.
  exists (Lf (fun f => (inverse_fun sig \co f)) A B);saw.
  apply:lf_bijective.
  - move => f /Zo_P[pa pb]; apply/Zo_P; split => //. 
    apply: (permutation_Sc (permutation_Si sigp) pa). 
  - move => u v /Zo_S up /Zo_S vp => /(f_equal (compose sig)).
    by rewrite (permutation_lK' sigp up)  (permutation_lK' sigp vp).
  - move => y /Zo_P[pa pb]; move:(permutation_lK sigp pa) => pc.
    exists (sig \co y) => //; apply/Zo_P; rewrite pc; split=> //.
    apply:(permutation_Sc sigp pa).
clear sigp T x xp.
set In := Nint n; set Iq := Nint q.
have: cardinal p0 = n.
    apply:(partition_nq_pr2 (CS_nat nN) qN (nesym (proj2 qp)) cardE p0p). 
rewrite -{1} (card_Nint nN) -/In => /card_eqP [fa [bfa sfa tfa]].
have bifa: bijection_prop (inverse_fun fa) In p0.
    hnf;aw; split => //;exact:(inverse_bij_fb bfa).
have fifa := proj1 (proj1 (proj31 bifa)).
pose fb:= graph  (inverse_fun fa).
have dfb: domain fb = In. 
  move:bifa => [/proj1/proj1 ra <- _]; exact: (domain_fg ra).
have rfb: forall i, inc i In -> inc (Vf (inverse_fun fa) i) p0.
  move:bifa => [ra rb rc] i iN; Wtac.
have rfb': forall i, inc i In -> inc (Vg fb i) p0 by [].
have injfb i j: inc i In -> inc j In ->  (Vg fb i) = (Vg fb j) -> i = j.
  by move => ii ji /(f_equal (Vf fa)); rewrite !(inverse_V bfa) // tfa.
have pfa1 : forall i, inc i In -> sub (Vg fb i) E.
  by move => i iN; apply /setP_P /ha /(rfb' _ iN).
have pfa:partition_w_fam fb E.
  move:bifa => [ra rb rc]; split. 
  - exact: (proj32 fifa).
  - apply:(mutually_disjoint_prop1 fifa); rewrite rb => i j y ii ji sa sb.
    case:(hc _ _ (rfb _ ii) (rfb _ ji)) => //; last by move => di; empty_tac1 y.
    apply:(injfb _ _ ii ji).
  - set_extens t; first by move/setUb_P => [y ya yb]; apply: pfa1 yb; ue.
    rewrite - hb;move/setU_P => [y ya yb]; apply/setUb_P; exists (Vf fa y).
      rewrite dfb - tfa; Wtac; fct_tac.
    by rewrite -/(Vf _ _) inverse_V2 // sfa.
have pfa2:forall x,singl_val2 (inc^~ In) (fun z=> inc x (Vg fb z)).
   move:(pfa) => [ra rb rc] x; rewrite -dfb  /= => i j  ii rd jj re.
   case: (rb _ _ ii jj) => // di; empty_tac1 x.
pose fc x:= select (fun z => inc x (Vg fb z)) In.
have pfa3: forall x, inc x E -> inc x (Vg fb (fc x)) /\ inc (fc x) In.
  move:(pfa) => [ra rb rc].
  move => x xE; apply:(select_pr) (pfa2 x).
  by move:xE; rewrite - rc - dfb => /setUb_P.
pose fi i:= equipotent_ex (Vg fb i) Iq.
have fibig: forall i, inc i In -> bijection_prop (fi i) (Vg fb i) Iq.
  move => i id; apply /equipotent_ex_pr/card_eqP.
  move:bifa => [ra rb rc].
  by rewrite (card_Nint qN)  -/(Vf _ _); apply: he; Wtac; rewrite rb - dfb.
set sPhi:= permutations In  \times (gfunctions In (permutations Iq)).
have ->: Ex59_den q n = cardinal sPhi.
  have ra:=(card_Nint nN). 
  have rb: finite_set In by apply/NatP; rewrite ra.
  have ra':=(card_Nint qN). 
  have rb': finite_set Iq by apply/NatP; rewrite ra'.
  rewrite - cprod2_pr1 - cprod2cl - cprod2cr (card_permutations rb) ra.
  move /card_eqP: (Eq_fun_set In (permutations Iq)) => <-.
  by rewrite cpow_pr1 ra (card_permutations rb') ra'.
have sphi_p1: forall x, inc x sPhi -> 
   [/\ pairp x, inc (P x) (permutations In) &
     forall i, inc i In -> inc (Vg (Q x) i) (permutations Iq)].
  move => x /setX_P [ra rb /gfunctions_P2 [rc1 rc2 rc3]]; split => //.
  by move => i ii; apply: rc3; apply: (inc_V_range rc1); rewrite rc2.
pose h1 x i t :=  
   (Vf (inverse_fun (fi (Vf (P x) i))) (Vf (Vg (Q x) i) (Vf (fi i) t))).
have h1p: forall x i t, inc x sPhi -> inc i In -> inc t (Vg fb i) ->
    inc (h1 x i t) (Vg fb (Vf (P x) i)) /\ inc  (h1 x i t)  E.
  move => x i t /sphi_p1 [_ /permutationsP ra rb] ii th; rewrite /h1.
  move:(fibig _ ii) => [/proj1/proj1 sa sb sc].
  have: inc (Vf (fi i) t) Iq by Wtac.
  set y := (Vf (fi i) t) => sd.
  move: (rb _ ii) => /permutationsP [wa1 wa2 wa3].
  set z := (Vf (Vg (Q x) i) y). 
  have zp: inc z Iq by rewrite/z;  Wtac; fct_tac.
  have ji: inc (Vf (P x) i) In by move: ra => [[[ra1 _] _] ra2 <-]; Wtac.
  move: (inverse_bij_bp (fibig _ ji)) => [se sf sg]; set a := Vf _ _.
  have aej: inc a (Vg fb (Vf (P x) i)) by rewrite /a; Wtac; fct_tac.
  split => //;exact:(pfa1 _ ji _ aej).
have h1p':  forall x i,  inc x sPhi -> inc i In ->
   lf_axiom (h1 x i) (Vg fb i) E.
  move => x i ra rb t tx; exact: (proj2 (h1p _ _ t ra rb tx)).
pose h2 x i := Lf (h1 x i) (Vg fb i) E.
have h2a: forall  x i, 
  inc x sPhi -> inc i In ->  function_prop (h2 x i)  (Vg fb i) E.
  rewrite /h2 => x i ra rb;saw;apply: (lf_function (h1p' _ _ ra rb)).
pose h3 x := common_ext fb (h2 x) E.
have h3p1: forall x, inc x sPhi ->
    function_prop (h3 x) E E /\
    (forall i, inc i (domain fb) -> agrees_on (Vg fb i) (h3 x) (h2 x i)).
  move => x xs; apply: (extension_partition1 pfa) => i; rewrite dfb //; fprops.
have h3p2: forall x i t, inc x sPhi -> inc i (Nint n) -> inc t (Vg fb i) ->
   Vf (h3 x) t = h1 x i t /\ inc (Vf (h3 x) t) (Vg fb (Vf (P x) i)).
  move => x i t ra rb rc; move: (proj1 (h1p _ _ t ra rb rc)).
  move: (proj2 (h3p1 _ ra)); rewrite  dfb =>rd; move: (rd  _ rb) => [qa qb qc].
  rewrite (qc t rc) /h2 LfV// => //; exact (h1p' _ _ ra rb).
have h3p3: forall x, inc x sPhi -> inc (h3 x) (permutations E).
  move => x xs; move: (proj1 (h3p1 _ xs)) => [ra rb rc].
  apply/permutationsP; split => //; apply:bijective_if_same_finite_c_inj.
      rewrite rb rc //.
    rewrite rb; apply /NatP; rewrite cardE;fprops.
  split => // t1 t2 ; rewrite rb; move/pfa3 => [rd re] /pfa3 [rf rg].
  move: (h3p2 _ _ _ xs re rd) (h3p2 _ _ _ xs rg rf) =>[pa pb][pc pd] eq1.
  move:(sphi_p1 _ xs) => [_ /permutationsP [[[fp ip] _] sp tp] xpb].
  case: (equal_or_not (fc t1) (fc t2)) => eq2; last first.
     rewrite - sp in re rg; case: eq2; apply: (ip _ _ re rg).
     have sa: inc (Vf (P x) (fc t1)) In by Wtac.
     have sb: inc (Vf (P x) (fc t2)) In by Wtac.
    rewrite - eq1 in pd; exact: (pfa2 _ _ _ sa pb sb pd).
  move: eq1; rewrite pa pc - eq2 /h1.
  rewrite - eq2 in rf.
  have sb: inc (Vg (Q x) (fc t1)) (permutations Iq) by apply: xpb.
  move: sb;  set sig0 := (Vg (Q x) (fc t1)); move /permutationsP=> [ua ub uc].
  move: (fibig _ re) => [[[sa' sb'] _] sd' se'] => h.
  rewrite sd' in sb'; apply: (sb' t1 t2 rd rf).
  have t1as: inc (Vf (fi (fc t1)) t1) (source sig0) by rewrite ub; Wtac.
  have t2as: inc (Vf (fi (fc t1)) t2) (source sig0) by rewrite ub; Wtac.
  apply: (proj2 (proj1 ua) _ _ t1as t2as).
  have: inc (Vf (P x) (fc t1)) In by Wtac.
  move /(fibig) /inverse_bij_bp => [[[_ sa''] _ ] sb'' _].
  apply: sa'' => //; rewrite sb''; Wtac; fct_tac.
set TT := Zo _ _.
have h3p4:  forall x i, inc x sPhi -> inc i In ->
   (Vf (extension_to_parts (h3 x)) (Vg fb i)) = (Vg fb (Vf (P x) i)).
  move => x i xs iN.
  move: (proj1 (h3p1 _ xs)) => [fh3 sh3 th3].
  have pb: sub (Vg fb i) (source (h3 x)) by rewrite sh3; exact: (pfa1 i iN).
  rewrite (etp_V (proj31 fh3) pb). 
  set_extens t.
    move => /(Vf_image_P fh3 pb) [u ua ->].
    exact:(proj2 (h3p2 _ _ _ xs iN ua)).
  move => ta; apply/(Vf_image_P fh3 pb). 
  move: (proj32 (sphi_p1 _ xs)) => /permutationsP [xa xb xc].
  have tb: inc (Vf (P x) i) In by Wtac; fct_tac.
  pose u:= Vf (inverse_fun (h3 x)) t.
  have tc: inc t (target (h3 x)) by rewrite th3;exact (pfa1 _ tb _ ta).
  have td:bijection (h3 x) by move:(h3p3 _ xs) => /permutationsP [].
  have td':=(bijective_inv_f td).
  have uE: inc u E by rewrite  - sh3 - ifun_t; apply:Vf_target; aw. 
  move: (pfa3 _ uE) => [te tf].
  have tv: t = Vf (h3 x) u by rewrite /u (inverse_V td tc). 
  exists u => //.
  move: (h3p2 x (fc u) u xs tf te) => [tg th]; rewrite - tv in th.
  have tx:inc (Vf (P x) (fc u)) In by  Wtac; fct_tac.
  move: (pfa2 t  (Vf (P x) i) (Vf (P x) (fc u)) tb ta tx th) => www.
  by move: (proj2 (proj1 xa)); rewrite xb => ii; rewrite (ii _ _ iN tf www).
have h3p5:  forall x, inc x sPhi -> inc (h3 x) TT.
  move => x xs; move: (h3p3 _ xs) => hp; apply:Zo_i => //.
  move /permutationsP:hp => [bh3 sh3 th3].
  have fh3: function (h3 x) by fct_tac.
  have pa: function (extension_to_parts (h3 x)) by apply: etp_f; fct_tac.
  have pb:sub p0 (source (extension_to_parts (h3 x))).
     rewrite lf_source sh3 //.
  move: (sphi_p1 _ xs) => [_ /permutationsP [wa wb wc] _].
  rewrite /F /extension_p3; set_extens t.
    move/(Vf_image_P pa pb) => [ u up ->].
    have [i iN <-]: exists2 i, inc i In & (Vg fb i) = u.
       have usa:inc u (source fa) by ue.
       exists (Vf fa u); first by  Wtac; fct_tac.
       rewrite -/(Vf _ _) inverse_V2 //.
    rewrite (h3p4 _ _ xs iN) -/(Vf _ _) - sfa - ifun_t; Wtac.
    rewrite ifun_s tfa; Wtac; fct_tac.
  rewrite -{1} sfa => ts.
  have ->: t = Vg fb (Vf fa t) by rewrite -/(Vf _ _) (inverse_V2 bfa ts). 
  move: (Vf_target (proj1 (proj1 bfa)) ts); rewrite tfa - wc => ra.
  move: (proj2 (proj2 wa) _ ra) => [y yt ->]; rewrite wb in yt.
  have rb:=(rfb' _ yt).
  by apply (Vf_image_P pa pb);ex_tac;rewrite (h3p4 _ _  xs yt).
pose repi i :=  (Vf (inverse_fun (fi i)) \0c).
have ra: forall i, inc i In -> inc (repi i) (Vg fb i).
  move=> i iN. 
  move:(fibig _ iN) => [bfi sfi tfi].
  have ifi:= bijective_inv_f  bfi.
  rewrite /repi - sfi - ifun_t; apply: (Vf_target ifi); rewrite ifun_s tfi.
  by apply /(NintP qN).
have h3p7:forall u v, inc u sPhi -> inc v sPhi -> h3 u = h3 v -> u = v.
  move => u v up vp sh3.
  move:(sphi_p1 _ up)(sphi_p1 _ vp) =>[pu pu1 pu2][pv pv1 pv2].
  have rb: P u = P v.
    move/permutationsP:pu1 =>[btu stu ttu].
    move/permutationsP:pv1 =>[btv stv ttv].
    move: (proj1 (proj1 btu)) (proj1 (proj1 btv)) => fu fv.
    apply:(function_exten fu fv); try ue.
    rewrite stu => i iN.
    have qa:=(ra _ iN).
    move: (proj2 (h3p2 _ _ _ up iN qa)) (proj2 (h3p2 _ _ _ vp iN qa)).
    rewrite - sh3; set t := Vf _ _ => i1 i2.
    have i3:inc (Vf (P u) i) (domain fb) by rewrite dfb; Wtac.
    have i4:inc (Vf (P v) i) (domain fb) by rewrite dfb; Wtac.
    case: (proj32 pfa _ _ i3 i4) => // di; empty_tac1 t.
  apply:(pair_exten pu pv rb).
  move /setX_P: (up) => [_ _] /Zo_P [_][pu3 pu4].
  move /setX_P: (vp) => [_ _] /Zo_P [_][pv3 pv4].
  have pu5: domain (Q u) = domain (Q v) by ue.
  apply:(fgraph_exten pu3 pv3 pu5); rewrite - pu4 => i iN.
  move /permutationsP: (pu2 _ iN) => [qu1 qu2 qu3].
  move /permutationsP: (pv2 _ iN) => [qv1 qv2 qv3].
  have ss: source (Vg (Q u) i) = source (Vg (Q v) i) by rewrite qv2.
  have tt: target (Vg (Q u) i) = target (Vg (Q v) i) by rewrite qv3.
  apply: (function_exten (proj1 (proj1 qu1))  (proj1 (proj1 qv1)) ss tt).
  clear pu pv pv1 pu2 pu3 pu4 pu5 pu2 pv2 pv3 pv4 ss tt.
  rewrite qu2 => k kq.
  move:(fibig i iN) => [sa sb sc].
  have sa':= (bijective_inv_f sa).
  set t := Vf (inverse_fun (fi i)) k.
  have ts: inc t (Vg fb i) by rewrite - sb /t - ifun_t; Wtac; aw; rewrite sc.
  move: (proj1 (h3p2 _ _ _ up iN ts)) (proj1 (h3p2 _ _ _ vp iN ts)).
  rewrite sh3 => ->; rewrite /h1 - rb.
  have ->: (Vf (fi i) t) = k by rewrite (inverse_V sa) // sc.
  have /fibig [se sf sg]: inc (Vf (P u) i) In.
     move/permutationsP: pu1 => [[[ff _] _] sf <-]; Wtac.
  move /(f_equal (Vf (fi (Vf (P u) i)))). 
  rewrite !inverse_V // sg;Wtac;fct_tac.
have h3p6: forall y, inc y TT -> exists2 x, inc x sPhi & y = h3 x.
  move => f /Zo_P [/permutationsP [bpf sfp tfp]];rewrite /F/extension_p3 => hf.
  have ff: function f by fct_tac.
  have ra': forall i, inc i In -> inc (Vf f (repi i)) E. 
    move => i iN; have ria:= (pfa1 _ iN _ (ra _ iN)); Wtac.
  pose tau i := fc (Vf f (repi i)).
  have rb: forall i, inc i In -> inc (tau i) In.   
    move => i iN; exact: (proj2 (pfa3 (Vf f (repi i)) (ra' _ iN))).
  have fef:=(etp_f (proj31 ff)).
  have p0s: sub p0 (source (extension_to_parts f)) by rewrite lf_source sfp.
  have rc: forall i, inc i In ->
     Vf (extension_to_parts f) (Vg fb i) = Vg fb (tau i).
    move => i iN; set x := LHS.
    have xp: inc  x p0. 
      have sa:inc (Vg fb i) p0 by apply: rfb'.
      by rewrite - hf; apply/(Vf_image_P fef p0s); ex_tac.
    have ss: inc x (source fa) by ue.
    move: (inverse_V2 bfa ss); set i1 := Vf fa x; rewrite /Vf -/fb => xv. 
    have i1N:inc i1 In by rewrite /i1; Wtac; fct_tac.
    move: (proj32 pfa i1 (tau i)); rewrite dfb - xv => rc.
    have rd: sub (Vg fb i) (source f) by rewrite  sfp; fprops.
    case:(rc i1N (rb _ iN)); first by move ->.
    move: (proj1 (pfa3 _ (ra' _ iN))) => xx du; empty_tac1 (Vf f (repi i)). 
    rewrite xv /x (etp_V (proj31 ff) rd);apply/Vf_image_P => //.
    move: (ra _ iN)=> re; ex_tac.
  have rd: inc (Lf tau In In) (permutations In).
    have inf:finite_set In by apply /NatP; rewrite (card_Nint nN).
    apply/permutationsP; saw;apply:bijective_if_same_finite_c_inj;aw; trivial.
    apply:(lf_injective rb) => u v ui vi sv.
    have hx i: inc i In -> inc (Vg fb i) (source (extension_to_parts f)).
      by rewrite lf_source sfp => iN; apply:ha; apply: rfb'.
    move:(rc _ ui); rewrite sv -(rc _ vi) => sa.
    move: (proj2 (etp_fi (proj1 bpf)) _ _ (hx _ ui) (hx _ vi) sa).
    apply: (injfb _ _ ui vi).
  have re: forall i, inc i In -> lf_axiom (Vf f) (Vg fb i) (Vg fb (tau i)).
    move => i iN t ta.
    have sff: sub (Vg fb i) (source f) by rewrite sfp; apply: (pfa1 _ iN).
    rewrite - (rc _ iN) (etp_V (proj31 ff) sff);apply /(Vf_image_P ff sff).
    ex_tac.
  have rf: forall i, inc i In -> bijection (Lf (Vf f) (Vg fb i)(Vg fb (tau i))).
    move => i iN.
    have cs:=(he _ (rfb' _ iN)).
    have cc: cardinal (Vg fb i) = cardinal (Vg fb (tau i)).
      by rewrite cs he //; apply:rfb'; apply: rb.
    have fss:finite_set (Vg fb i) by apply /NatP; rewrite cs.
    have ax:= (re _ iN).
    apply:bijective_if_same_finite_c_inj; aw; trivial.
    have sff: sub (Vg fb i) (source f) by rewrite sfp; apply: (pfa1 _ iN).
    by apply: lf_injective =>// u v /sff us /sff vs;apply:(proj2 (proj1  bpf)).
  pose si i s := (Vf (fi (tau i)) (Vf f (Vf (inverse_fun (fi i)) s))).
  pose s' i:= ((fi (tau i) \co Lf (Vf f) (Vg fb i) (Vg fb (tau i))) \co
           inverse_fun (fi i)).
  have sia: forall i s, inc i In -> inc s Iq ->
     [/\ (bijection_prop (s' i) Iq Iq), 
       si i s =  Vf (s' i) s &  inc (si i s) Iq].
    move => i s iI sS; rewrite /s';set f' := Lf _ _ _. 
    move:(fibig _ iI) (fibig _ (rb _ iI))(rf _ iI) => [qa qb qc][qd qe qf] qg.
    have qh: source f' = (Vg fb i) by rewrite lf_source.
    have qi: target f' = (Vg fb (tau i)) by rewrite lf_target.
    have pa:inc s (target (fi i)) by rewrite qc.
    have pb':function (fi (tau i)) by fct_tac.
    have pb'':function f' by fct_tac.
    have pb: fi (tau i) \coP f' by hnf;rewrite qe qi. 
    have pc: function (fi (tau i) \co f') by fct_tac.
    have pd':=(bijective_inv_f qa).
    have pd:(fi (tau i) \co f') \coP inverse_fun (fi i). 
      hnf; aw; rewrite qh qb; split => //.
    have pe:inc (Vf (inverse_fun (fi i)) s) (source f'). 
      by rewrite qh - qb - ifun_t; Wtac; aw.
    have pe':inc (Vf (inverse_fun (fi i)) s) (Vg fb i) by rewrite - qh.
    have pf :=  (re _ iI).
    have ba:=(compose_fb (inverse_bij_fb qa) (compose_fb qg qd pb) pd).
    split; first by hnf; aw; rewrite qc qf.
       by rewrite /f' ! compfV// ? LfV//; aw.
    by rewrite /si; Wtac; rewrite qe; apply:pf.
  have sax i:inc i In -> lf_axiom (si i) Iq Iq.
      move => iN t ts; exact:(proj33 (sia _ _ iN ts)).
  have sib: forall i, inc i In -> inc (Lf (si i) Iq Iq) (permutations Iq).
    move => i iN; apply /permutationsP; hnf; saw.
    have zq: inc \0c Iq by apply/(NintP qN).
    have [sa sb sc]:= (proj31 (sia _ _ iN zq)).
    have -> //: (Lf (si i) Iq Iq) =  s' i.
    have ax:= (sax _ iN).
    have sd: function (Lf (si i) Iq Iq) by apply:(lf_function ax).
    apply:function_exten; [ exact | fct_tac | by rewrite lf_source | |].
      by rewrite lf_target.
    rewrite lf_source => s sq; rewrite LfV//; exact:(proj32 (sia _ _ iN sq)).
  pose x := J  (Lf tau In In) (Lg In (fun i => (Lf (si i) Iq Iq))). 
  have xphi: inc x sPhi by apply:(setXp_i rd); apply: gfunctions_i1.
  ex_tac.
  move:(proj1 (h3p1 _ xphi)) => [qa qb qc].
  apply:(function_exten ff qa); [ by rewrite qb | by rewrite qc |  ]. 
  move => y /=; rewrite sfp => yE. 
  move:(pfa3 y yE)=> [qd qe].
  move:(fibig _ qe) => [qf qg qh].
  move:(fibig _ (rb _ qe)) => [qf' qg' qh'].
  have qi: inc y (source (fi (fc y))) by ue.
  have qj:inc (Vf (fi (fc y)) y) Iq by Wtac; fct_tac.
  move: (re _ qe _ qd); rewrite - qg' => qj'.
  rewrite (proj1 (h3p2 _ _ _  xphi qe qd))  /h1 /x pr1_pair pr2_pair. 
  rewrite (LfV rb qe) (LgV qe) (LfV (sax _ qe) qj) /si (inverse_V2 qf qi).
  by rewrite (inverse_V2 qf' qj').
pose Phi:= Lf h3 sPhi TT.
symmetry; apply/card_eqP; exists Phi; split;rewrite /Phi;aw; trivial.
by apply: lf_bijective.
Qed.

Lemma Exercise5_9a q E: finite_set E ->
   natp (cardinal (partition_nq E q)).
Proof.
move => fE; apply/NatP.
have h: sub (partition_nq E q) (partitions E) by apply: Zo_S.
have h': sub (partitions E) (\Po (\Po E)) by apply: Zo_S.
apply:(sub_finite_set (sub_trans h h')). 
by apply:setP_finite; apply:setP_finite.
Qed.

Lemma Exercise5_9b q n: natp n -> natp q -> 
  [/\ natp(Ex59_num q n), natp(Ex59_den q n) & natp (Ex59_val q n) ].
Proof.
move => nN qN.
have ha :=(NS_factorial (NS_prod qN nN)).
have hb := (NS_prod (NS_factorial nN) (NS_pow (NS_factorial qN) nN)).
by split => //; apply: NS_quo. 
Qed.

Lemma Exercise5_9b' q n: natp n -> natp q -> (Ex59_den q n)  <> \0c.
Proof.
move => nN qN; apply:(cprod2_nz (factorial_nz nN)).
exact:(cpow_nz (factorial_nz qN)).
Qed.
 
Lemma Exercise5_9c q n: natp n -> natp q -> \0c <c q ->
   (Ex59_den q n) %|c (Ex59_num q n). 
Proof.
move => nN qN qp.
set E:= Nint (q *c n).
have ce: cardinal E = q *c n by apply: (card_Nint (NS_prod qN nN)).
rewrite -(partition_nq_pr9 nN qN qp ce) cprodC.
apply:cdivides_pr1 (proj32 (Exercise5_9b nN qN)).
apply: Exercise5_9a; apply/NatP; rewrite ce; fprops.
Qed.


Lemma Exercise5_9c' q n: natp n -> natp q -> \0c <c q ->
  (Ex59_num q n) = (Ex59_val q n) *c (Ex59_den q n).
Proof.
move => nN qN qp.
by rewrite (cdivides_pr (Exercise5_9c nN qN qp)) cprodC.
Qed.

Lemma Exercise5_9d q n: natp n -> natp q -> \0c <c q ->
   (Ex59_val q n) <> \0c.
Proof.
move => nN qN qp dz.
move:(Exercise5_9c' nN qN qp). rewrite dz cprod0l.
apply: (factorial_nz (NS_prod qN nN)).
Qed.

Lemma Exercise5_9e E q n: natp n -> natp q -> \0c <c q -> 
  cardinal E = q *c n -> 
  cardinal (partition_nq E q) = Ex59_val q n.
Proof.
move => nN qN qp cE.
move:(Exercise5_9b nN qN) => [ha hb hc].
have /(Exercise5_9a q) hd: finite_set E by apply/NatP; rewrite cE; fprops.
move: (esym (partition_nq_pr9 nN qN qp cE)); rewrite (cprodC (cardinal _)) => h.
exact:(cdivides_pr2 ha hb hd (Exercise5_9b' nN qN) h).
Qed.

Lemma Exercise5_9f n: natp n -> 
  (Ex59_val \0c n) = Yo (n <=c \1c) \1c \0c.
Proof.
move => nN.
move: (cleSltP NS1); rewrite succ_one => H.
have cfN:=(NS_factorial nN); have cfn:= CS_nat cfN.
rewrite /Ex59_val /Ex59_num /Ex59_den cprod0l factorial0 cpow1x (cprod1r cfn).
case: (equal_or_not n \0c) => n0.
  by rewrite n0 factorial0 (cquo_one NS1) (Y_true (cle_01)).
case: (equal_or_not n \1c) => n1.
  by rewrite n1 factorial1 (cquo_one NS1) (Y_true (cleR CS1)).
have ln2:=(cge2 (CS_nat nN) n0 n1).
move /H: (ln2) => /cltNge gn1.
move:(factorial_monotone nN ln2); rewrite factorial2 => /H dg.
by rewrite (cquo_small cfN dg) (Y_false gn1).
Qed.

Lemma Exercise5_9f': partition_nq emptyset \0c = C1.
Proof.
rewrite / partition_nq /partitions  setP_00. apply: set1_pr.
  apply:Zo_i; last by move => x /in_set0.
  apply:Zo_i;[ fprops |split; last by move => x /in_set0 ].
  by split; [ rewrite setU_0 | move => x y /in_set0 ].
move => x /Zo_P [/Zo_P [ha [_ hb]] hc];case: (emptyset_dichot x)=> // - [t tx].
by move:(card_nonempty1 (hb _ tx) (hc _ tx)). 
Qed.


Definition Ex59b_num1 q n k := (q *c n) -c k *c (q -c \1c).
Definition Ex59b_num q n k := factorial (Ex59b_num1 q n k).
Definition Ex59b_den q n k := 
   (factorial k)*c(factorial (n-c k)) *c (factorial q) ^c (n-c k).
Definition Ex59b_val q n k:= (Ex59b_num q n k) %/c (Ex59b_den q n k).

Lemma Exercise5_9g q n k: natp n -> natp q -> natp k -> 
  [/\ natp(Ex59b_num1 q n k), natp(Ex59b_num q n k),
     natp (Ex59b_den q n k), natp(Ex59b_val q n k) & (Ex59b_den q n k) <> \0c].
Proof.
move => nN qN kN.
have pa: natp (Ex59b_num1 q n k) by apply: NS_diff; apply:(NS_prod qN nN).
have pb: natp (Ex59b_num q n k) by apply: NS_factorial.
have pc: natp (n -c k) by apply: NS_diff.
have pd: natp (Ex59b_den q n k). 
  apply:NS_prod; first by apply:NS_prod; apply:NS_factorial.
  apply:(NS_pow (NS_factorial qN) pc).
have pe:Ex59b_den q n k <> \0c.
  apply:cprod2_nz; first by apply:cprod2_nz; apply:factorial_nz.
  by apply:cpow_nz;apply:factorial_nz.
by split => //; apply:NS_quo.
Qed.

Lemma Exercise5_9h q n k: natp n -> natp q -> natp k -> k <=c n -> \0c <c q ->
  (Ex59b_num q n k) =  (Ex59b_den q n k) *c 
    ((binom (Ex59b_num1 q n k) k) *c (Ex59_val q (n -c k))).
Proof.
move => nN qN kN sa sb.
move:(Exercise5_9g nN qN kN) => [ha hb hx hd he].
have sb': \1c <=c q by apply/cge1P.
have hf:=(cdiff_pr sa). 
have hf':=(cdiff_pr sb').
move:(NS_diff k nN)(NS_diff \1c qN) => n'N q'N.
have ea: Ex59b_num1 q n k = (n -c k) *c q +c k.
   rewrite /Ex59b_num1 -{1} hf -{1 3} hf'. 
   rewrite cprodDl (cprod1l (CS_sum2 _ _)) !cprodDr (cprod1r (CS_nat n'N)).
   have ra:=(NS_sum nN (NS_prod q'N n'N)).
   rewrite(cprodC _ k)(csumC (k *c _)) csumA hf (cdiff_pr1 ra (NS_prod kN q'N)).
   by rewrite (csumC _ k) cprodC csumA hf.
have ea': Ex59b_num1 q n k -c k = (n -c k) *c q. 
  by rewrite ea (cdiff_pr1 (NS_prod n'N qN) kN).
have hg: (k <=c Ex59b_num1 q n k) by rewrite ea; apply:(Nsum_Mle0 _ kN).
rewrite /Ex59b_num  /Ex59b_den - (binom_good ha kN hg) ea' (cprodC _ q).
rewrite -/(Ex59_num q (n -c k)) (Exercise5_9c' n'N qN sb).
rewrite /Ex59_den - (cprodA (factorial k)).
set b := _ *c _ ^c _. rewrite (cprodC _ b).
set a := binom _ _;set c := factorial  _.
by rewrite cprodACA cprodA (cprodC a).
Qed.

Lemma Exercise5_9h' q n k: natp n -> natp q -> natp k -> k <=c n -> \0c <c q ->
  (Ex59b_val q n k) = (binom (Ex59b_num1 q n k) k) *c (Ex59_val q (n -c k)).
Proof.
move => nN qN kN lkn qp.
move: (Exercise5_9g nN qN kN) => [ha hb hc hd he].
have hf:=(proj33 (Exercise5_9b (NS_diff k nN) qN)).
rewrite /Ex59b_val (Exercise5_9h nN qN kN lkn qp).
by rewrite (cdivides_pr4 hc (NS_prod (NS_binom ha kN) hf) he).
Qed.


Definition Ex59_int q j := Nintcc j (j +c (q -c \1c)).
Definition Ex59_intervalp q x := 
   exists2 j, natp j & x = Ex59_int q j.

Definition Ex59_nb_int q p := 
   cardinal (Zo p (Ex59_intervalp q)).

Definition Ex59_k_interval E q k :=
  Zo (partition_nq E q) (fun p => Ex59_nb_int q p = k).


Lemma Exercise5_9i E q n: natp n -> natp q -> cardinal E = q *c n -> \0c <c q ->
  partition_w_fam (Lg (Nintc n) (Ex59_k_interval E q))  (partition_nq E q).
Proof.
move => nN qN cE qp.
split; first fprops.
  hnf;aw => i j iN jN; rewrite !LgV//; mdi_tac nij => x /Zo_hi ha /Zo_hi hb.
  by case:nij; rewrite - ha -hb.
set_extens t.
   by move/setUb_P => [y yI];rewrite Lgd in yI; rewrite LgV//; move/Zo_S.
move => tp; apply /setUb_P; aw.
have ct:=(partition_nq_pr2 (CS_nat nN) qN (nesym (proj2 qp)) cE tp).
have lkn: inc (Ex59_nb_int q t) (Nintc n). 
  by apply/(NintcP nN); rewrite - ct; apply/sub_smaller/Zo_S.
by ex_tac; rewrite LgV//; apply:Zo_i.
Qed.

Lemma Exercise5_9i' E q n: 
  natp n -> natp q -> cardinal E = q *c n -> \0c <c q ->
  cardinal (partition_nq E q) = 
    csumb (Nintc n) (fun k => (cardinal (Ex59_k_interval E q k))).
Proof.
move => nN qN cE qp.
move:(Exercise5_9i nN qN cE qp) => [_ ha <-].
by rewrite (csum_pr4 ha);aw; apply:csumb_exten => k kn; rewrite LgV.
Qed.

Lemma Nintcc_exten a b c d: 
   a <=c b -> natp b -> Nintcc a b = Nintcc c d ->
   a = c /\ b = d.
Proof.
move => lab bN ss.
have aN := NS_le_nat lab bN.
have laa:= cleR (proj31 lab).
have lbb:= cleR (proj32 lab).
have: inc a (Nintcc a b) by apply/Nint_ccP.
  rewrite ss => /Nint_ccP [ [cN _ lca] [_ dN _]].
have: inc b (Nintcc a b) by apply/Nint_ccP.
  rewrite ss => /Nint_ccP [ _ [_ _ lbd]]. 
have lcc := cleR (proj31 lca).
have ldd := cleR (proj32 lbd).
have lcd := (cleT lca (cleT lab lbd)).
have: inc c (Nintcc a b) by rewrite ss; apply/Nint_ccP.
  move/Nint_ccP => [ [_ _ /(cleA lca) <- ] _].
have: inc d (Nintcc a b) by rewrite ss; apply/Nint_ccP.  
by move/Nint_ccP => [ _ [_ _ /(cleA lbd) <- ]].
Qed.

Lemma Nintcc_exten_spec q i j: natp q -> natp i ->
   Nintcc i (i +c (q -c \1c)) = Nintcc j (j +c (q -c \1c)) ->
   i = j.
Proof.
move => qN iN eqa.
have la: i <=c (i +c (q -c \1c)) by apply:csum_M0le; fprops.
have bN: natp (i +c (q -c \1c)) by apply: (NS_sum iN (NS_diff _ qN)).
exact: (proj1 (Nintcc_exten la bN eqa)).
Qed.

Lemma Ex59_intp q i: natp q -> \0c <c q -> natp i ->
   i +c q = csucc (i +c (q -c \1c)).
Proof.
move => qN qp iN.
have sb': \1c <=c q by apply/cge1P.
have dN:=(NS_diff \1c qN).
have cq:cardinalp (q -c \1c) by apply:CS_diff.
by rewrite - (csum_nS _ dN) (csucc_pr4 cq) (csumC _ \1c) (cdiff_pr sb').
Qed.

Lemma Ex59_interval_prop q j: natp j -> natp q -> \0c <c q ->
  forall x, inc x (Nintcc j (j +c (q -c \1c))) <->
       j <=c x /\ x <c j +c q.
Proof.
move => jN qN qp x.
have sdN:= NS_sum jN (NS_diff \1c qN).
rewrite (Ex59_intp qN qp jN).
split.
  by move/Nint_ccP => [[xN _ la] [_ _ lb]]; split => //;apply/(cltSleP sdN).
move => [la /(cltSleP sdN) lb]. 
by have xN := NS_le_nat lb sdN; apply/Nint_ccP.
Qed.


Definition Ex59_int_lb q x :=  select (fun j => x = Ex59_int q j) Nat.
Definition Ex59_splitA q p := 
  fun_image (Zo p (Ex59_intervalp q)) (Ex59_int_lb q).
Definition Ex59_splitA' q p := fun_image (Ex59_splitA q p) (Ex59_int q).
Definition Ex59_splitB q p := p -s (Ex59_splitA' q p).

Lemma Exercise5_9j1 q x (j := Ex59_int_lb q x):
  natp q -> \0c <c q ->  Ex59_intervalp q x ->
  x =  Ex59_int q j /\ natp j.
Proof.
move => qN qp h; apply: (select_pr h). 
move => a b /= aN av bN bv. 
rewrite av in bv; exact:( Nintcc_exten_spec qN aN bv).
Qed.

Lemma Exercise5_9j2 q x (j := Ex59_int_lb q x):
  natp q -> \0c <c q ->  Ex59_intervalp q x -> x = Ex59_int q j.
Proof. move => ha hb hc; exact: (proj1 (Exercise5_9j1 ha hb hc)). Qed.

Lemma Exercise5_9j3 q p j:  natp q -> \0c <c q ->
  inc j (Ex59_splitA q p) -> (natp j /\ inc (Ex59_int q j)  p).
Proof.
move => qN qp /funI_P [z /Zo_P [za zb] zc].
by move:(Exercise5_9j1 qN qp zb); rewrite - zc; move => [<- jN].
Qed.

Lemma Exercise5_9j4 q p: natp q -> \0c <c q ->
  Zo p (Ex59_intervalp q) = Ex59_splitA' q p. 
Proof.
move => qN qp.
set_extens t.
  move => tv; move:(tv)=> /Zo_P[ti it]; apply /funI_P.
  rewrite(Exercise5_9j2 qN qp it).
  by exists (Ex59_int_lb q t); [ apply/funI_P; ex_tac | ].
move/funI_P =>[z /funI_P [u  uz ->] ->].
by rewrite -(Exercise5_9j2 qN qp (Zo_hi uz)).
Qed.

Lemma Exercise5_9j5 E n q p k: 
  natp n -> natp q -> \0c <c q -> cardinal E = q *c n ->
  inc p (Ex59_k_interval E q k) ->  
   cardinal (Ex59_splitA q p) = k /\ cardinal (Ex59_splitA' q p) = k.
Proof.
move => nN qN qp cE /Zo_P [pq pb].
set T:= (Ex59_splitA q p). pose W:= (Exercise5_9j2 qN qp).
suff ct: cardinal T = k.
   split; [ exact | rewrite - ct; apply:cardinal_fun_image].
   move => a b /funI_P [z /Zo_hi zv ->].
   by move /funI_P => [z' /Zo_hi zv' ->]; rewrite - (W _ zv) - (W _ zv') => ->.
rewrite -pb; apply:cardinal_fun_image.
move => i j /Zo_P [ha hb]/Zo_P [hc hd] ee.
by rewrite (W _ hb) (W _ hd) ee.
Qed.

Lemma Exercise5_9j6 E n q p k: 
  natp n -> natp q -> \0c <c q -> cardinal E = q *c n ->
  inc p (Ex59_k_interval E q k) ->  
   cardinal (Ex59_splitB q p) = n -c k.
Proof.
move => nN qN qp cE px.
move:(proj2 (Exercise5_9j5 nN qN qp cE px)) => ck.
have ha: sub (Ex59_splitA' q p) p. 
  by rewrite - (Exercise5_9j4 _ qN qp); apply:Zo_S.
move:px => /Zo_S pp.
have cp:=(partition_nq_pr2 (CS_nat nN) qN (nesym (proj2 qp)) cE pp).
have fsp: finite_set p by  apply/NatP; rewrite cp.
by rewrite /Ex59_splitB (cardinal_setC4 ha fsp) ck cp.
Qed.

Definition Ex59_Jprop q n k J:=
  [/\ cardinal J = k, sub J Nat,
  (forall i j, inc i J -> inc j J -> i <c j -> i +c q <=c j) &
  (forall j, inc j J -> j +c q <=c q *c n)].

Lemma Exercise5_9k1 n q p k (E:= Nint (q *c n)):
  natp n -> natp q -> \0c <c q -> 
  inc p (Ex59_k_interval E q k) -> Ex59_Jprop q n k  (Ex59_splitA q p).
Proof.
move => nN qN qp pI.
move:(pI) => /Zo_S /Zo_P [/partitionsP [[pp cp] _ ] _].
have ce:cardinal E = q *c n by apply:card_Nint; fprops.
set J := (Ex59_splitA q p).
have JN: sub J Nat by  move => t tJ; exact:proj1(Exercise5_9j3 qN qp tJ).
have cJ:= (proj1 (Exercise5_9j5 nN qN qp ce pI)).
split => //.
  move => i j /(Exercise5_9j3 qN qp) [iN ip] /(Exercise5_9j3 qN qp) [jN jp].
  move => [lij nij].
  case: (cleT_el (CS_sum2 i q) (CS_nat jN)) => // la.
  move/(Ex59_interval_prop iN qN qp) : (conj lij la) => jii.
  move: (csum_Meqlt jN qp); rewrite (csum0r (CS_nat jN)) => ljn.
  have  jij: inc j (Nintcc j (j +c (q -c \1c))). 
    apply/(Ex59_interval_prop jN qN qp); split; fprops.
  case: (cp _ _ ip jp) => di; last by empty_tac1 j.
  case: nij; exact (Nintcc_exten_spec qN iN di).
move => i /(Exercise5_9j3 qN qp) [iN ip].
have la: i <=c (i +c (q -c \1c)) by apply:csum_M0le; fprops.
have ea:=(Ex59_intp qN qp iN).
have bi := NS_sum iN (NS_diff \1c qN).
set j := (i +c (q -c \1c)).
have jI: inc j (Nintcc i (i +c (q -c \1c))).
   apply/(Ex59_interval_prop iN qN qp); split; first exact.
   rewrite ea;  apply /(cltSleP bi); fprops.
have /(NintP (NS_prod qN nN)) : inc j E by rewrite - pp;union_tac.
by move /(cleSltP bi); rewrite - ea.
Qed.

Lemma Exercise5_9k2 n q k J (e := nth_elt J): 
  natp k -> Ex59_Jprop q n k J ->
  [/\ forall x y, x <c y -> y <c k -> e x <c e y, 
      forall x y, x <=c y -> y <c k -> e x <=c e y, 
      forall x y, x <c k -> y <c k -> e x = e y -> x = y,
      forall x, x <c k -> inc (e x) J &
      forall y, inc y J -> exists2 i, i <c k & y = e i].     
Proof.
move => kN [ sa sb _ _].
have ra:forall x y, x <c y -> y <c k -> e x <c e y.
  move => x y lxy lyk. 
  by apply: (nth_elt_monotone (NS_lt_nat lyk kN) sb) lxy; rewrite sa.
have rc:forall x, x <c k -> inc (e x) J.
  by move => x lxk; apply: (nth_elt_inK (NS_lt_nat lxk kN) sb); rewrite sa.
split => //.
+ move => x y ha hb; case: (equal_or_not x y).
    by move => ->; apply/cleR/CS_nat/sb/rc.
  move => nxy; exact (proj1(ra _ _ (conj ha nxy) hb)).
+ move => x y lxk lyk exy; case: (cleT_ell (proj31_1 lxk) (proj31_1 lyk)) => //.
  - by move => lxy; case: (proj2 (ra _ _ lxy lyk)).
  - by move => lxy; case: (proj2 (ra _ _ lxy lxk)).
+ move => y yJ.
  rewrite - sa in kN.
  by move:(nth_elt_surj sb kN yJ) => [x]; rewrite sa => xa xb; exists x.
Qed.


Lemma Exercise5_9k3 n q k J (e := nth_elt J): 
  natp k -> Ex59_Jprop q n k J ->
  (forall i, i<c k -> q *c i <=c e i) /\ 
  (forall j, j <c k -> e j +c q <=c q *c n). 
Proof.
move => kN JP; move:(Exercise5_9k2 kN JP) =>[jpa _ _  jpd _].
move: JP => [cJ JN jp1 jp2].
split; last by  move => i /jpd /jp2.
move => i ik; move: (NS_lt_nat ik kN) => iN; move: i iN ik.
apply: Nat_induction. 
  move => kp;rewrite cprod0r; apply:(cle0n (JN _ (jpd _ kp))).
move => i iN Hi lik.
have lisi:= (cltS iN).
have lt2:= (clt_ltT lisi lik).
apply:cleT (jp1 _ _ (jpd _ lt2) (jpd _ lik) (jpa _ _ lisi lik)).
rewrite (cprod_nS _ iN); apply:csum_Mleeq ; exact: (Hi lt2).
Qed.

Lemma Exercise5_9k4 n q k J (e:= nth_elt J) (e' := fun i => e i -c q *c i): 
  natp q -> natp n -> k <=c n -> Ex59_Jprop q n k J ->
  [/\ forall i, i <c k -> natp (e' i),
   (forall i, i <c k -> e i = e' i +c q *c i),
   (forall i j, i <=c j -> j <c k -> e' i <=c e' j) &
  (forall j, j <c k -> e' j <=c q *c (n -c k)) ].
Proof.
move => qN nN lkn h.
have kN:= NS_le_nat lkn nN.
move:(Exercise5_9k2 kN h) =>[jpa _ _  jpd _].
move:(Exercise5_9k3 kN h) => [pa pb].
move: h => [cJ JN jp1 jp2].
have pc:(forall i, i <c k -> e i = e' i +c q *c i).
  by move => i ik; rewrite /e' csumC (cdiff_pr  (pa _ ik)).
have K: forall i, i <c k -> natp (e' i).
  by move => i /jpd/JN eN; apply:NS_diff.
have pd': forall i, natp i -> csucc i <c k -> e' i <=c e' (csucc i).
  move => i iN sik.
  have sa:=(cltS iN); have sd := (NS_lt_nat sik kN); have se:= (clt_ltT sa sik).
  move: (jpd _ se) (jpd _ sik) => sb sc.
  move:(jp1 _ _ sb sc (jpa _ _ sa sik)).
  rewrite -/(e i) -/(e _)(pc _ se) (pc _ sik) - csumA  - (cprod_nS _ iN). 
  apply:(csum_le2r (NS_prod qN sd) (K _ se) (K _ sik)). 
have pd: forall i j, i <=c j -> j <c k -> e' i <=c e' j.
  move => i j lij ljk. 
  move: (NS_lt_nat (cle_ltT lij ljk) kN) => iN.
  have kp:=(cle_ltT (cle0x (proj31_1 ljk)) ljk).
  move: (cpred_pr kN (nesym (proj2 kp))) => [sa sb].
  move: ljk; rewrite sb; move/(cltSleP sa); move: j lij. 
  apply:(Nat_induction3 iN sa); first by apply: (cleR (CS_diff _ _)).
  move => j jn jlk hr; apply:(cleT hr); apply: (pd' _ (NS_lt_nat jlk sa)).
  by rewrite sb;  apply:cltSS. 
split => // j jk.
have kp:=(cle_ltT (cle0x (proj31_1 jk)) jk).
move: (cpred_pr kN (nesym (proj2 kp))) => [sa sb].
move:(cltS sa); rewrite - sb => lt1.
move:(jk); rewrite sb; move/(cltSleP sa) => l2; apply:(cleT(pd _ _ l2 lt1)).
move:(pb _ lt1); rewrite -/(e _) (pc _ lt1) -{1}(cdiff_pr lkn).
rewrite - csumA - (cprod_nS _ sa) - sb cprodDr csumC.
apply:(csum_le2l (NS_prod qN kN) (K _ lt1) (NS_prod qN (NS_diff k nN))).
Qed.


Lemma Exercise5_9k5 n q k J (e:= nth_elt J) (e' := fun i => e i -c q *c i)
  (T := functions_incr_nat k (csucc (q *c (n -c k)))):
  natp q -> natp n -> k <=c n -> Ex59_Jprop q n k J ->
  inc (Lf e' k (csucc (q *c (n -c k)))) T /\
  cardinal T = binom ((q *c (n -c k)) +c k) k.
Proof.
move => qN nN lkn h.
have kN := NS_le_nat lkn nN.
have tN:=(NS_prod qN (NS_diff k nN)).
split; last by apply: card_increasing_nat.
move:(Exercise5_9k4 qN nN lkn h) => [sa sb sc sd].
set f := Lf _ _ _.
have ax:lf_axiom e' k (csucc (q *c (n -c k))).
  move =>  x /(NltP kN) lxk.
  move:(sa _ lxk) NS0 (sd _ lxk) => eN zN es.
  by apply/(NleP tN). 
 have fa: inc f (functions  k (csucc (q *c (n -c k)))).
   by apply/functionsP;rewrite/f; saw; apply:lf_function.
apply/(increasing_nat_prop kN (NS_succ tN)); split => //.
move =>x y lxy lyk.
have xI: inc x k by apply/(NltP kN); exact(cle_ltT lxy lyk).
have yI: inc y k by apply/(NltP kN).
rewrite /f !LfV//; apply:(sc _ _ lxy lyk).
Qed.


Lemma Exercise5_9k6 n q k f 
  (J := fun_image k (fun i => Vf f i +c q *c i))
  (T := functions_incr_nat  k (csucc (q *c (n -c k)))):
  natp q -> natp n -> k <=c n -> \0c <c q -> inc f T ->
  [/\ Ex59_Jprop q n k J,
    forall i, i <c k -> (nth_elt J i) = Vf f i +c q *c i &
    forall i, i <c k -> (nth_elt J i)  -c q *c i = Vf f i].
Proof.
move => qN nN lkn qp.
have kN := NS_le_nat lkn nN.
have tN:=(NS_prod qN (NS_diff k nN)).
move/(increasing_nat_prop kN (NS_succ tN)) => [/functionsP  [ff sf tf] ficf].
have tfn i: inc i k -> natp (Vf f i).
  rewrite - sf => zz.
  by move:(Vf_target ff zz); rewrite tf; move/ (NS_inc_nat (NS_succ tN)).
have JN: sub J Nat. 
  move => i /funI_P [z zz ->].
  exact: (NS_sum (tfn _ zz) (NS_prod qN (NS_inc_nat kN zz))).
have inc2 i j: inc i k -> inc j k -> i <c j ->
     Vf f i +c q *c i <c Vf f j +c q *c j.
  move => iI jI lij.
  move/(NltP kN): (jI)  => ljk.
  have li2 :=(ficf i j (proj1 lij) ljk).  
  apply:(csum_Mlelt (tfn _ jI) li2).  
  apply:(cprod_Meqlt qN (NS_lt_nat ljk kN) lij (nesym (proj2 qp))).
have inc3 i j:  inc i k -> inc j k -> 
     Vf f i +c q *c i <c Vf f j +c q *c j -> i<c j.
  move => iI jI h.
  case:(NleT_ell (NS_inc_nat kN iI) (NS_inc_nat kN jI)) => // lij.
  - by case: (proj2 h); rewrite lij.
  - case: (cltNge (inc2 _ _ jI iI lij) (proj1 h)).
have cj:cardinal J = k.
  rewrite -(card_card (CS_nat kN)); apply:cardinal_fun_image => i j iI jI eq1.
  case:(NleT_ell (NS_inc_nat kN iI) (NS_inc_nat kN jI))  => // lij.
    by case:(proj2 (inc2 _ _ iI jI lij)).    
  by case:(proj2 (inc2 _ _ jI iI lij)).    
have si2 u v: inc u J -> inc v J -> u <c v -> u +c q <=c v.
  move => /funI_P [i iI ->] /funI_P [j jI ->] h.
  move:(inc3 _ _ iI jI h) (NS_inc_nat kN  iI) => lij iN.
  move/(NltP  kN): jI => ljk.
  rewrite - csumA;apply:(csum_Mlele (ficf _ _ (proj1 lij) ljk)). 
  by rewrite - (cprod_nS _ iN); apply: cprod_Meqle;apply/(cleSltP iN). 
have si4 j: inc j J -> j +c q <=c q *c n.
  move =>  /funI_P [i iI ->]; rewrite - csumA.
  have iN:= (NS_inc_nat kN iI).
  move/(NltP kN): (iI) => lik.
  have le1: (q *c i +c q) <=c q *c k.
    by rewrite - (cprod_nS _ iN); apply: cprod_Meqle;apply/(cleSltP iN). 
   move: iI;rewrite - sf => zz. 
  move:(Vf_target ff zz); rewrite tf => /(NleP tN) le2.
  by move:(csum_Mlele le2 le1); rewrite - cprodDr (csumC _ k) (cdiff_pr lkn).
have enuu:forall i, i <c k -> nth_elt J i = Vf f i +c q *c i.
  have ha1:forall i, i <c k -> natp (Vf f i +c q *c i).
    move => i /(NltP kN) ik; apply:JN; apply/funI_P; ex_tac.
  have ha2 i j:i <c j -> j <c k -> Vf f i +c q *c i <c Vf f j +c q *c j.
    move => lij h1; apply:(inc2)(lij); apply/(NltP kN) => //.
    exact:(clt_ltT lij h1).
  exact:(nth_elt_exten kN ha1 ha2).
have Jp: Ex59_Jprop q n k J by [].
move: (Exercise5_9k4 qN nN lkn Jp) => [sa sb sc sd].
split => // i ik; rewrite (enuu _ ik); apply:cdiff_pr1. 
   by apply:tfn; apply/(NltP kN).
exact: (NS_prod qN (NS_lt_nat ik kN)).
Qed.

Definition Ex59_compl n q J :=
  Nint (q *c n) -s union (fun_image J (Ex59_int q)).

Definition Ex59_Cprop n q J k p:=
  [/\ inc p (partition_nq (Ex59_compl n q J) q),
   cardinal p = n -c k & forall x, inc x p -> ~ (Ex59_intervalp q x)].


Lemma Exercise5_9l1 n q p (E:= Nint (q *c n)):  
  natp n -> natp q -> \0c <c q -> 
  inc p (partition_nq E q) -> 
   Ex59_compl n q (Ex59_splitA q p) = union (Ex59_splitB q p).
Proof.
move => nN qN qp /Zo_P [/partitionsP [[ha hb] hc] hd].
rewrite/Ex59_compl /Ex59_splitB /Ex59_splitA'.
set J := (Ex59_splitA q p).
set iv := (fun j : Set => Nintcc j (j +c (q -c \1c))).
rewrite -/E - ha.
set_extens t. 
  move/setC_P => [/setU_P [z sa zb]] zc; apply /setU_P; exists z => //.
  apply/setC_P; split => // /funI_P [v vj zv]; case: zc; union_tac.
  apply/funI_P; ex_tac.
move/setU_P => [z za /setC_P [zb zc]]; apply/setC_P; split; first union_tac.
move/setU_P => [v va /funI_P[j jj jv]]; case: zc.
move:(Exercise5_9j3 qN qp jj). rewrite -/(iv _) - jv; move => [jN jp].
apply/funI_P; ex_tac; rewrite - jv.
by case:(hb _ _ zb jp) => // di; empty_tac1 t.
Qed.

Lemma Exercise5_9l2 n q p (E:= Nint (q *c n)):  
  natp n -> natp q -> \0c <c q -> 
  inc p (partition_nq E q) -> 
  inc (Ex59_splitB q p) (partition_nq (Ex59_compl n q (Ex59_splitA q p)) q). 
Proof.
move => nN qN qp pp.
have ha:=(Exercise5_9l1 nN qN qp pp).
move/Zo_P: pp => [/partitionsP [[qa qb] qc] qd].
apply/Zo_P; split; last by move => x /setC_P [/qd].
apply/partitionsP; split;last by move => x /setC_P [/qc].
by split =>// a b /setC_P [ ap _] /setC_P [ bp _]; apply: qb.
Qed.

Lemma Exercise5_9l3 n q p k (E:= Nint (q *c n)):  
  natp n -> natp q -> \0c <c q -> 
  inc p (Ex59_k_interval E q k) -> 
  Ex59_Cprop n q (Ex59_splitA q p) k (Ex59_splitB q p). 
Proof.
move => nN qN qp pi.
have ce:cardinal E = q *c n by apply:card_Nint; fprops.
have cp:=(Exercise5_9j6 nN qN qp ce pi).
split => //.
  apply:Exercise5_9l2 => //; apply/Zo_S: pi.
rewrite /Ex59_splitB - (Exercise5_9j4 _ qN qp).
by move => x /setC_P [xp /Zo_P xx] xe; case:xx.
Qed.

Lemma Exercise5_9l4 n q p k J x y:
  natp n -> natp q -> \0c <c q -> 
  Ex59_Cprop n q J k p -> inc x p -> inc y x -> y <c q *c n.
Proof.
move => nN qN qp [/Zo_P [/partitionsP [[ha _] _]]] _ _ _ xp yp.
have nqN:=NS_prod qN nN.
have /setC_P [/(NintP nqN) //]: inc y (Ex59_compl n q J). 
by rewrite - ha; union_tac.
Qed.

Definition Ex59_pos_in_J J k x :=
   intersection ((Zo (Nint k) (fun i => x <=c nth_elt J i)) +s1 k).

Lemma Exercise5_9l5 J x: Ex59_pos_in_J J \0c x = \0c.
Proof.
rewrite /Ex59_pos_in_J Nint_co00; set y := Zo _ _.
have ->: y = emptyset by apply/set0_P => t / Zo_S /in_set0.
by rewrite set0_U2 setI_1.
Qed.

Lemma Exercise5_9l6 q n k J: 
  Ex59_Jprop q n k J -> natp k -> \0c <c k ->
 [/\ forall x,  Ex59_pos_in_J J k x  <=c k,
    forall x,  Ex59_pos_in_J J k x = \0c <-> (forall y, inc y J -> x <=c y),
    forall x, natp x ->
      (Ex59_pos_in_J J k x = k <-> (forall y, inc y J -> y <c x)),
    forall x, (exists2 y, inc y J & x <=c y) -> 
      (exists2 y, inc y J & y <c x) ->
     (\0c <c  Ex59_pos_in_J J k x /\  Ex59_pos_in_J J k x <c k) &
    forall x, let i := Ex59_pos_in_J J k x in 
     \0c <c i -> i <c k -> 
    [/\ inc (nth_elt J i) J,  x <=c (nth_elt J i),
     inc (nth_elt J (cpred i)) J & (nth_elt J (cpred i)) <c x ]]. 
Proof.
move => Jp kN kp. 
pose Ex x := (Zo (Nint k) (fun i=> x <=c nth_elt J i) +s1 k).
pose lEx x := intersection (Ex x).
have ha: forall x, sub (Ex x) (Nintc k).
   move => x t /setU1_P; case. 
    by move =>/Zo_S /(NintP kN) [ /(NintcP kN)].
  move => ->; apply/(NintcP kN); fprops.
have hb x: inc (lEx x) (Ex x) /\ forall y, inc y (Ex x) ->  (lEx x) <=c y.
  have px: sub (Ex x) Nat by move => t/ha /Nint_S.
  have pa: ordinal_set (Ex x) by move => t /px/OS_nat. 
  have pb: nonempty (Ex x) by exists k; apply: setU1_1.
  move:(least_ordinal0 pa pb); rewrite -/(lEx x); move => [sa sb sc].
  split => // y ya.  
  exact: (ocle3 (CS_nat (px _ sb))  (CS_nat (px _ ya)) (sc _ ya)). 
have hc x: (lEx x) <=c k. apply/(NintcP kN); exact (ha _ _ (proj1 (hb x))).
move: (Exercise5_9k2 kN Jp) => [jp1 jp2 jp3 jp4 jp5].
have ra x: lEx x = \0c -> (forall y, inc y J -> x <=c y).
  move => pp; move: (proj1 (hb x)); rewrite pp; case/setU1_P; last first.
   by move => kz; case: (proj2 kp).
  move/Zo_hi =>xs y /jp5 [j ljk ->].
  exact:(cleT xs (jp2 _ _ (cle0x (proj31_1 ljk)) ljk)).
have rb: forall x, (forall y, inc y J -> x <=c y) ->  lEx x = \0c.
  move => x hx.
  have /(proj2(hb x))/cle0//: inc \0c (Ex x). 
  apply:setU1_r; apply:Zo_i; first by apply/(NintP kN).
  exact:(hx _ (jp4 _ kp)).
move:Jp =>[wa JN _ _].
have rc:  forall x, natp x -> lEx x = k -> (forall y, inc y J -> y <c x).
  move => x xN lk; move: (hb x) => [_]; rewrite lk => xb.
  move => y /jp5 [i ik ->]; case:(NleT_el xN (JN _ (jp4 _ ik))) => // xc.
  have: inc i (Ex x) by apply setU1_r; apply:Zo_i => //; apply/(NintP kN).
  by move /xb => /(cltNge ik).
have rd: forall x, (forall y, inc y J -> y <c x) -> lEx x = k.
  move => x hx; move: (hb x) => [xa xb].
  by case /setU1_P:xa => // /Zo_P [/(NintP kN) /jp4/hx sa /cleNgt []].
have re: forall x, (exists2 y, inc y J & x <=c y) -> 
    (exists2 y, inc y J & y <c x) ->
     (\0c <c lEx x /\ lEx x <c k). 
  move => x [y1 y1j la] [y2 y2j lb].
  have nN:=(NS_le_nat la (JN _ y1j)).
  have hcx := hc x.
  split. 
    by apply:(card_ne0_pos (proj31 hcx)) => /ra ee; case:(cleNgt (ee _ y2j)).
  by split => // /(rc _ nN) ee;case: (cltNge (ee _ y1j)).
split => //.
- move => x; split;fprops.
- move => x; split;fprops.
-  move => x i xa xb; move:(hb x) => [/setU1_P xc xd].
  case: xc; [ move/Zo_hi => xe | by move => h; case: (proj2 xb) ].
  have sa:= (jp4 _ xb).
  have sc:= (cpred_lt (NS_lt_nat xb kN) (nesym (proj2 xa))).
  have sb' := (clt_ltT sc xb).
  have sb:= (jp4 _ sb').
  split => //; case: (NleT_el (NS_le_nat xe (JN _ sa))(JN _ sb)) => // xh.
  have /xd /cleNgt sd //: inc (cpred (lEx x)) (Ex x).
  by apply:setU1_r; apply: Zo_i => //; apply/(NintP kN).
Qed.

Lemma Exercise5_9l6bis q n k J j x :
  Ex59_Jprop q n k J -> natp k -> \0c <c k -> natp x ->
  j <c k -> j <> \0c -> (nth_elt J (cpred j)) <c x -> x <=c (nth_elt J j) ->
  Ex59_pos_in_J J k x = j.
Proof.
move => H kN kp xN ljk jna ha hb.
move:(Exercise5_9l6 H kN kp) => [ra rb rc rd re].
move: (Exercise5_9k2 kN H) => [jp1 jp2 jp3 jp4 jp5].
have K u v: u <c v -> v <c k -> nth_elt J (cpred v) <c nth_elt J u -> False.
  move => luv lvk lt1.
  move: (cpred_pr (NS_lt_nat lvk kN) (card_gt_ne0 luv)) => [ua ub].
  have la: u <=c  cpred v by apply /(cltSleP ua); rewrite - ub.
  case:(cleNgt (jp2 _ _ la (cle_ltT (cpred_le (proj31_1 lvk)) lvk)) lt1).
move: (cpred_pr (NS_lt_nat ljk kN) jna) => [ua ub].
have jJ: inc (nth_elt J j) J by apply: jp4.
have pjs: cpred j <c j by rewrite {2} ub; fprops.
have cpjk:=(clt_ltT pjs ljk).
move: (ra x); set v := Ex59_pos_in_J J k x; case /cle_eqVlt => vk.
  by move /(rc _ xN): vk => h; move:(cltNge (h _ jJ) hb).
case: (equal_or_not v \0c) => vz.
  by move/rb:vz => h; move:(cleNgt (h _ (jp4 _ cpjk)) ha).
have vz':=(card_ne0_pos (proj31_1 vk) vz).
move: (re _ vz' vk); rewrite -/v; move => [la lb lc ld].
move: (clt_leT ha lb) (clt_leT ld hb) => le lf.
case:(cleT_ell (proj31_1 vk) (proj32_1 pjs)) => // h.
- case: (K _ _ h ljk le).
- case: (K _ _ h vk lf).
Qed.

Lemma Exercise5_9l7 q n k J  (e := nth_elt J) (E' := (Ex59_compl n q J)):
  natp n -> natp q -> \0c <c q -> k <=c n ->
  Ex59_Jprop q n k J -> natp k -> \0c <c k ->
  (inc (cpred (q *c n)) E' \/
  ( (forall t, inc t E' -> t <c q *c (n -c k)) \/
    exists j, let x := (q *c ((n -c k) +c j)) in 
     [/\ j <c k, x <> \0c, e j = x, inc (cpred x) E' & 
     forall t, inc t E' -> t <=c (cpred x)])).
Proof.
move => nN qN qp lkn jP kN kp.
move: (Exercise5_9k2 kN jP) => [jp1 jp2 jp3 jp4 jp5].
move: (jP) =>[cJ JN jp6 jp7].
pose di i := q *c (n -c i -c \1c).
have qnN:= NS_prod qN nN.
have knz :=(nesym (proj2 kp)).
have q0:=(nesym (proj2 qp)).
have np := (clt_leT kp lkn).
have nnz := (nesym (proj2 np)).
have [pnN pnv ]:=(cpred_pr nN nnz). 
have cpq:= (cpred_pr4 (CS_nat qN)).
have cpk:= (cpred_pr4 (CS_nat kN)).
have lpkk:= (cpred_lt kN knz). 
have [pkN pkv]:= (cpred_pr kN knz).
have qnz:=(cprod2_nz q0 nnz).
have [yN yv]:=(cpred_pr qnN qnz).
have yE1:=(cpred_lt qnN qnz).
set y0 := cpred (q *c n) in yN yv yE1.
case: (inc_or_not y0 E') => yE; [by left | right].
have E'b t: inc t E' -> t <c q *c n by move => /setC_P [/(NintP qnN)].
have EN : sub E' Nat by move => t /E'b h;exact: (NS_lt_nat h qnN).
have div i: i <c n -> di i = q *c (n -c (csucc i)).
  move => licn; move:(NS_lt_nat licn nN) => iN.
  move:(Nsucc_rw iN) => sa; rewrite sa.
  rewrite /di;apply: f_equal; rewrite (cdiffA nN iN NS1) //; rewrite - sa.
  by apply/(cleSltP iN).
have div1 i: i <c n -> di i +c q *c (csucc i) = q *c n.
  move => licn; move:(NS_lt_nat licn nN) => iN.
  by rewrite (div _ licn) - cprodDr csumC (cdiff_pr) //; apply/(cleSltP iN).
have ddN i : natp (n -c i -c \1c) by apply:NS_diff; apply:NS_diff.
have diN i: natp (di i) by apply: (NS_prod qN (ddN i)). 
pose II j := (Nintcc j (j +c (q -c \1c))).
have IIP j: natp j -> forall x, inc x (II j) <-> j <=c x /\ x <c j +c q.
  move =>  jN x; apply:(Ex59_interval_prop jN qN qp).
have [j0 j0j yJ]: exists2 j, inc j  J & inc y0 (II j).
  case: (inc_or_not y0 (union (fun_image J II))) => yz.
    by move/setU_P: yz => [v va /funI_P [j ja  jb]]; ex_tac; rewrite - jb.
  by case: yE; apply/setC_P; split => //; apply/(NintP qnN).
have j1p:j0 +c q = q *c n.
  apply: cleA; first by move: (jP) => [_ _ _ sa]; exact:(sa _ j0j).
  move/(IIP _ (JN _ j0j)): yJ =>[_].
  by rewrite yv; move/(cleSlt0P (proj31_1 yE1) (NS_sum (JN _ j0j) qN)).
have j0v: j0 = di \0c. 
  rewrite /di (cdiff_n0 nN)(cprodBl qN nN NS1) - j1p (cprod1r (CS_nat qN)).
  by rewrite (cdiff_pr1 (JN _ j0j) qN).
have j0max: forall j, inc j  J -> j <=c j0.
  move => j r1;move: (jp7 _ r1); rewrite -j1p => r2.
  exact:(csum_le2r qN (JN _ r1) (JN _ j0j) r2).
have la0: e (k -c \1c) = di \0c.
  rewrite - cpk - j0v; apply:cleA; first exact:(j0max _ (jp4 _ lpkk)).
  move:(jp5 _ j0j) => [a a1 ->].
  move: a1; rewrite {1} pkv; move /(cltSleP pkN) => a1.
  by move: (jp2 a (cpred k) a1 lpkk). 
have div0 i p:  natp i -> natp p -> csucc i <c p ->
     csucc ((p -c csucc i) -c \1c) = ((p -c i) -c \1c).
  move => iN pN sa.
  have ea:= Nsucc_rw iN.
  have la: i +c \1c <=c p by move: (proj1 sa); rewrite ea.
  rewrite  (cdiffA pN iN NS1 la) - ea -(cpred_pr4 (CS_diff _ _)).
  by rewrite -(proj2 (cpred_pr (NS_diff (csucc i) pN) (cdiff_nz sa))).
have div2 i: natp i -> csucc i <c n -> di (csucc i) +c q = di i.
   move => iN sa;rewrite  -(cprod_nS _ (ddN _)) /di.
   rewrite (div0 _ _ iN nN sa); reflexivity.
set B := Zo (Nint k) (fun z => forall i, i <=c z -> inc (di i) J).
have oB: inc \0c B.
  have oo: inc \0c (Nint k) by apply/(NintP kN).
  by apply: (Zo_i oo) => i /cle0 ->; rewrite - j0v.
have neB: nonempty B by ex_tac.
have BI: sub B (Nint k) by apply:Zo_S.
have BN:= (sub_trans BI (@Nint_S1 k)).
have Bf:= (sub_finite_set BI (@finite_Nint k)).
move:(finite_subset_Nat BN Bf neB) => [i1 i1B i1a].
have li1n: i1 <c n by apply: clt_leT  lkn; move/(NintP kN): (BI _ i1B). 
have i1N:= (BN _ i1B).
have la: forall i,  i <=c i1 -> e (k -c i -c \1c) = di i.
  move => i ii; move:(NS_le_nat ii i1N) => iN.
  move: i iN ii; apply: Nat_induction.
   by rewrite (cdiff_n0 kN) la0.
  move => j jN Hr b1.
  set x := di (csucc j).
  have xJ: inc x J by apply: (Zo_hi i1B).
  have epx:=(Hr (cleT (cleS jN) b1)).
  have [a lak av]:= (jp5 _ xJ). 
  have cjln:=(cle_ltT b1 li1n).
  have : x <c di j. 
    rewrite - (div2 _ jN cjln); apply:(csum_M0lt (JN _ xJ) q0).
  rewrite av - epx => la.
  move /(NintP kN): (BI _ i1B) => lik1.
  move:(cle_ltT b1 lik1) => ltcjk.
  set b := (k -c csucc j) -c \1c.
  set c := (k -c j) -c \1c.
  have lb: c <c k.
    have ljk:=(cle_ltT (cleS jN) ltcjk).
    move:(cpred_pr (NS_diff j kN) (cdiff_nz ljk)) => [sa sb].
    rewrite /c  - (cpred_pr4 (CS_diff _ _)). apply/(cleSltP sa); rewrite - sb.
    apply:(cdiff_ab_le_a _ (CS_nat kN)).
  case: (cleT_el (proj31_1 lb) (proj31_1 lak) ) => lc.
    by move: (jp2 _ _ lc lak); move/(cltNge la).
  have bN: natp b by apply(NS_diff _ (NS_diff _ kN)).
  have bv1: csucc b = c by exact:(div0 _ _ jN kN ltcjk).
  have ld: a <=c b by apply/(cltSleP bN); rewrite bv1.
  case: (equal_or_not a  b) => ee; first by rewrite - ee.
  have lab: a <c b by split.
  have lf: b <c c by  rewrite - bv1; apply:(cltS bN).
  move:(jp1 _ _ lf lb); rewrite -/e epx => ra.
  have dijJ: inc (di j) J by rewrite - epx; exact: (jp4 _ lb).
  have su := (jp4 _ (clt_ltT lf lb)).
  move:(jp6 _ _ su dijJ ra).
  rewrite -(div2 j jN cjln) => /(csum_le2r qN (JN _ su) (diN (csucc j))) => t.
  by move:(jp1 _ _ lab (clt_ltT lf lb)); rewrite - av; move/(cleNgt t).
have cp1: forall t, inc t E' -> t <c di i1.  
  move => t tE; case: (NleT_el (diN i1) (EN _ tE)) => // h.
  move: (cdivision (EN _ tE) qN q0) => [QN RN [dvp rs]].
  move:(csum_Meqlt (NS_prod qN QN) rs) ;rewrite - dvp => lta.
  have ltb:q *c (t %/c q) <=c t.  
     by rewrite {2} dvp;apply:(Nsum_M0le _ (NS_prod qN QN)).
  have ltc: inc t (II (q *c (t %/c q))) by apply/(IIP _ (NS_prod qN QN)).
  move/setC_P: tE => [/(NintP qnN) ts /setU_P []]. 
  have ltd: (t %/c q) <c n by apply/(cprod_lt2l qN QN nN); apply: cle_ltT ts. 
  have xwx: t %/c q = (n -c (n -c csucc (t %/c q))) -c \1c.
    move /(cleSltP QN): ltd => sa.
    by rewrite (double_diff nN sa) -(cpred_pr4 (CS_succ _)) (cpred_pr2 QN).
  have lte: \1c <=c n -c i1 by apply/(cge1 (CS_diff n i1)) /(cdiff_nz li1n).
  have tJ: inc (q *c (t %/c q)) J. 
    move: lta; rewrite - (cprod_nS _ QN) => lta; move:(cle_ltT h lta).
    move/(cprod_lt2l qN (ddN i1) (NS_succ QN))=>/(cltSleP QN) => H.
    move: (csum_Meqle i1 (csum_Meqle \1c  H)). 
    rewrite (cdiff_pr lte) (cdiff_pr (proj1 li1n)) (csumC \1c) - (Nsucc_rw QN). 
    move => tt; rewrite xwx; apply:(Zo_hi i1B). 
    by apply: (cdiff_Mle i1N (NS_succ QN)).
  exists (II (q *c (t %/c q))) => //;apply /funI_P; ex_tac.
case: (equal_or_not i1 (cpred k)) => sa1.
  by left; move => t /cp1; rewrite (div _ li1n) sa1 - pkv. 
right.
have lt1: csucc i1 <=c k by  apply/(cleSltP i1N)/(NintP kN)/BI. 
have lt2: i1 <=c cpred k. 
  by apply/(cleSSP (proj31_1 li1n) (CS_nat pkN)); rewrite - pkv.
have lic : i1 <c cpred k by split.
  have lt3: csucc i1 <c k.
    by split => // h;move: (proj2 lic); rewrite - h; rewrite (cpred_pr2 i1N).
  have lci1n:=(clt_leT lt3 lkn).
  have Ha:= (cdiff_nz lci1n).
  have Hb: di i1 <> \0c by rewrite (div _ li1n); apply: (cprod2_nz q0).
  have Hc: inc (di i1) J by apply:(Zo_hi i1B _ (cleR (proj31 lt2))).
  case: (inc_or_not (di (csucc i1)) J) => Hd.
    have: inc (csucc i1) B. 
      apply /Zo_P; split; first by apply/(NintP kN).
      move => i /cle_eqVlt; case; first by move ->. 
      move /(cltSleP i1N); apply:(Zo_hi i1B).
    by move/i1a =>/(cltNge (cltS i1N)).
  move: (cpred_pr (diN i1) Hb) => []; set x := cpred (di i1) => xN xv.
  have He:inc x (Nint (q *c n)).  
    apply /(NintP qnN); apply: (clt_leT (cltS xN)); rewrite - xv.
    rewrite (div _ li1n); exact:(cprod_Meqle  _(cdiff_ab_le_a _ (CS_nat nN))).  
  have ra: forall t, inc t E' -> t <=c x.
    by move => t  tE; move: (cp1 _ tE); rewrite xv => /(cltSleP xN).
  have rb: inc x E'. 
    apply /setC_P; split; first exact.  
    move /setU_P => [s sa /funI_P [j ja jb]]; case: Hd.
    move: sa; rewrite jb; move /(IIP _ (JN _ ja)) => [hu hv].
    have wa: j <c (di i1) by  rewrite xv; apply/(cltSleP xN).
    move:(jp6 _ _ ja Hc wa); rewrite xv => sa.
    have: j +c q = di i1 by rewrite xv;apply:(cleA sa); apply/(cleSltP xN).
    by rewrite - (div2 _ i1N lci1n);move/(csum_eq2r qN (JN _ ja) (diN _))=> <-.
move: (la _ (cleR (proj31 lt2))); rewrite xv.
set j := k -c i1 -c \1c; move => ej1.
have jv: j = k -c csucc i1 by rewrite /j (cdiffA kN i1N NS1) - (Nsucc_rw i1N).
have ljk: j <c k. 
  rewrite jv; apply: (cdiff_Mlt kN kN (proj1 lt3)). 
  apply:(csum_M0lt kN (@succ_nz _)).
have jv2: ((n -c k) +c j) = (n -c (csucc i1)). 
   rewrite jv - {2} (cdiff_pr lkn) (cdiffA2  kN (NS_diff k nN) (proj1 lt3)). 
   by rewrite csumC.
have jv3: di i1 = (q *c ((n -c k) +c j)) by rewrite  jv2 (div _ li1n).
rewrite - xv in ej1.
by exists j; rewrite - jv3.  
Qed.




Lemma Exercise5_9l8 q n k J p (E':= union p) (e := nth_elt J)  (* 185 *)
  (e':= fun i => e i -c q *c i) (V:=  Ex59_pos_in_J J k)
  (V' := fun x => x -c  q *c (V x))
  (T:= Nint (q *c (n -c k))):
  natp n -> natp q -> \0c <c q -> k <=c n ->
  Ex59_Jprop q n k J -> natp k -> \0c <c k ->
  Ex59_Cprop n q J k p -> 
  [/\ forall x, inc x E' -> V x = k -> e'(k -c \1c) +c q *c k <=c x,
    forall x, inc x E' -> \0c <c (V x) -> (V x) <c k -> 
     e'( (V x) -c \1c) +c q *c (V x) <=c x /\ x <c  e'(V x) +c q *c (V x),
    forall x, inc x E' ->  q *c (V x) <=c x,
   forall x, inc x E' ->  x =  q *c (V x) +c V' x &
  order_isomorphism (Lf V' E' T) (graph_on cardinal_le E')
     (graph_on cardinal_le T)
   ].

Proof.
move => nN qN qp lkn jP kN kp pP.
move: (Exercise5_9l6 jP kN kp) => [ra rb rc rd re]. 
move: (Exercise5_9k2 kN jP) => [jp1 jp2 jp3 jp4 jp5].
move:(jP) =>[cJ JN _ _].
have qnN:= NS_prod qN nN.
have knz :=(nesym (proj2 kp)).
have ha: forall x, inc x E' -> V x <=c k.
   move => x _; apply: ra.
have hb:  forall x, inc x E' -> x <c q *c n.
  move => x /setU_P [y ya yb].
  apply:(Exercise5_9l4 nN qN qp pP yb ya).
have hb':  forall x, inc x E' -> natp x.
  move => x /hb h; exact:(NS_lt_nat h qnN).
have cpq:= (cpred_pr4 (CS_nat qN)).
have cpk:= (cpred_pr4 (CS_nat kN)).
have lpkk:= (cpred_lt kN knz). 
have [pkN pkv]:= (cpred_pr kN knz).
have Ev: E' = (Ex59_compl n q J) by move: pP => [/Zo_S /partitionsP [[]]].
have qa j x: inc x E' -> inc j J -> j <c x -> j +c q <=c x.
  move => xu; move:(xu) => /setU_P [y xy yp] jJ [le1 _].
  case: (cleT_el (CS_sum2 j q) (proj32 le1)) => // xa.
  move:xu;rewrite Ev => /setC_P [xb] []; apply /setU_P.
  exists (Nintcc j (j +c (q -c \1c))); last by apply/funI_P; ex_tac.
  by apply /(Ex59_interval_prop (JN _ jJ) qN qp).
have qa'' x: inc x J -> inc x E' -> False.
  move=>xJ;rewrite Ev => /setC_P [xb] []; apply /setU_P.
  have cx:= (CS_nat(Nint_S1 xb)).
  exists (Nintcc x (x +c (q -c \1c))); last by apply/funI_P; ex_tac.
  move: (csum_Meqlt (JN _ xJ)  qp); rewrite (csum0r cx) => la.
  apply /(Ex59_interval_prop (JN _ xJ) qN qp); split; fprops.
have qa' j x: inc x E' -> inc j J -> x <=c j -> x <c j.
  move => xu jJ le1; split => // exj;rewrite exj in xu; case: (qa'' _ jJ xu).
have hb'':= (jp4 _ lpkk).
move:(Exercise5_9k4 qN nN lkn jP) => [jp7 jp8 jp9 jp10].
have hc: forall x, inc x E' -> V x = k -> e'(k -c \1c) +c q *c k <=c x.
  move => x xe; move/(rc _ (hb' _ xe)) => H; move:{H} (H _ hb'')=> ww.
  rewrite - cpk [in q *c k] pkv (cprod_nS _ pkN) csumA -(jp8 _ lpkk).
  exact: (qa _ _ xe hb'' ww).
have e0J: inc (e \0c) J by apply: (jp4 _ kp).
have hc'': forall x, inc x E' -> V x = \0c -> x <c e'\0c.
  move => x xe /rb h;  rewrite /e' cprod0r (cdiff_n0 (JN _ e0J)).
  apply: (qa' _ _ xe e0J); apply:(h _ e0J).
have hd: forall x, inc x E' -> \0c <c (V x) -> (V x) <c k -> 
     e'( (V x) -c \1c) +c q *c (V x) <=c x /\ x <c  e'(V x) +c q *c (V x).
  move => x xE la lb.
  move: (re x la lb); rewrite -/(V x); move => [qa1 qb1 qc1 qd1].
  rewrite -(cpred_pr4 (proj32_1 la)). 
  split; last by rewrite -(jp8 _ lb); exact:(qa' _ _ xE qa1 qb1).
  have lc:=(cpred_lt (NS_lt_nat lb kN) (nesym (proj2 la))).
  have [pvN pvv]:= (cpred_pr  (NS_lt_nat lb kN) (nesym (proj2 la))).
  rewrite [in q *c _] pvv (cprod_nS _ pvN) csumA  -(jp8 _  (clt_ltT lc lb)).
  exact:(qa _ _ xE qc1 qd1).
have he:  forall x, inc x E' -> q *c (V x) <=c x.
  move => x xE; move:(ha _ xE) => la.
  case: (equal_or_not (V x) k) => lb.
    move:(hc _ xE lb); rewrite lb; apply:cleT.
    apply:csum_Mle0; fprops.
  case: (equal_or_not (V x) \0c) => lc.
    by rewrite lc (cprod0r); apply:(cle0n (hb' _ xE)).
  have vp:=(card_ne0_pos (proj31 la) lc).  
  apply:cleT(proj1(hd _ xE vp (conj la lb))). 
  apply:csum_Mle0; fprops.
have hf: forall x, inc x E' ->  x =  q *c (V x) +c V' x.
  by move => x xE; rewrite(cdiff_pr (he _ xE)).
have hf': forall x, inc x E' -> natp (V' x).
   move => x /hb' xN; apply:(NS_diff _ xN).
have prop2 x: inc x E' -> V x <> k -> V' x <c e' (V x). 
  move => xE vzk;have ltvk :=(conj (ra x) vzk).
  have: q *c (V x) +c V' x <c q *c (V x) +c e' (V x).
    rewrite - (hf _ xE) csumC;case:(equal_or_not (V x) \0c) => vz. 
       have w:=(hc'' _ xE vz).
       by rewrite vz cprod0r (csum0r (proj32_1 w)).
    exact: (proj2 (hd _ xE (card_ne0_pos (proj31 (ra x)) vz) ltvk)).
  exact:(csum_lt2l (NS_prod qN (NS_le_nat (ra x) kN)) (hf' _ xE) (jp7 _ ltvk)).
have scV' x x': inc x E' -> inc x' E' -> x <c x' -> V' x <c V' x'.
  move => xE xE' lxx.
  move: (ra x) (ra x'); rewrite -/(V x) -/(V x') => lvk lvk'.
  move:(hb' _ xE)(hb' _ xE') => xN xN'.
  case: (equal_or_not (V x') \0c) => vz'.
    move/(rb x'): (vz') => lt1.
    case: (equal_or_not (V x) \0c) => vz.
      by rewrite /V' vz vz' cprod0r !cdiff_n0.
    have w: forall z, inc z J -> z <c x -> False.
      move => z zJ sa; case:(cltNge (clt_ltT sa lxx) (lt1 _ zJ) ).
    case: (equal_or_not (V x) k) => lv2.
      move /(rc x xN): lv2 => lv3; case: (w _ e0J (lv3 _ e0J)).
    have lv3:=(card_ne0_pos (proj31 lvk) vz).
    move: (re _ lv3 (conj lvk lv2)); rewrite -/(V x); move => [_ _ zJ zv].
    case: (w _ zJ zv).
  have vzp':=(card_ne0_pos (proj31 lvk') vz').
  case: (equal_or_not (V x) k) => vzk.
    move/(rc _ xN): (vzk) => lt1.
    case: (equal_or_not (V x') k) => vzk'.
      move: lxx; rewrite {1}(hf _ xE) {1} (hf _ xE') vzk vzk'.
      apply:(csum_lt2l (NS_prod qN kN) (hf' _ xE) (hf' _ xE')).
    move: (re _ vzp' (conj lvk' vzk')) => [sa sb _ _].
    case:(cltNge  (clt_ltT (lt1 _ sa) lxx) sb).
  have ltvk :=(conj lvk vzk).
  have sc := (NS_le_nat lvk kN).
  have sc' := (NS_le_nat lvk' kN).
  move:(cpred_pr sc' vz') => [v''N v''v]; have v'v:= (cpred_pr4(proj31 lvk')).
  have vx'1k: V x' -c \1c <c k. 
    by rewrite - v'v; apply/(cleSltP v''N); rewrite -v''v.
  have qvN:=(NS_prod qN sc).
  have prop1: e' (V x' -c \1c) <=c V' x'.
      have sa: q *c (V x') +c e' (V x' -c \1c)  <=c q *c (V x') +c V' x'.
        rewrite csumC - (hf _ xE'); case: (equal_or_not (V x') k) => vzk'.
          by move: (hc _ xE' vzk'); rewrite vzk'.
        exact: (proj1 (hd _ xE' vzp' (conj lvk' vzk'))).
      apply:(csum_le2l (NS_prod qN sc')(jp7 _ vx'1k) (hf' _ xE')) sa.
  case: (equal_or_not (V x) (V x')) => sv.
    move: lxx; rewrite {1} (hf _ xE) {1} (hf _ xE') - sv.
    exact:(csum_lt2l qvN (hf' _ xE) (hf' _ xE')).
  suff h: e' (V x) <=c e' (V x' -c \1c).
     exact:(clt_leT (clt_leT (prop2 _ xE vzk) h) prop1).
  apply: (jp9 _ _ _ vx'1k);rewrite -v'v; apply /(cltSleP v''N); rewrite -v''v.
  split; last exact.
  case:(equal_or_not (V x) \0c) => vz; first by rewrite vz; exact (proj1 vzp').
  have vzp:=(card_ne0_pos (proj31 lvk) vz).
  case:(equal_or_not (V x') k) => vzk'; first by rewrite vzk'.
  case: (cleT_el (proj31 lvk) (proj31 lvk')) => // ll.
  move:(cpred_pr sc vz) => [vwN vwv].
  have tt: V x' <=c cpred (V x) by apply /(cltSleP vwN); rewrite - vwv.
  case: (cleNgt (jp2 _ _ tt (cle_ltT (cpred_le (proj31 lvk)) ltvk))).
  move: (re _ vzp ltvk)  (re _ vzp' (conj lvk' vzk')) => [_ _ _ td] [_ tb' _ _].
  exact:(clt_leT (clt_ltT td lxx) tb').
have scV'' x x': inc x E' -> inc x' E' -> x <=c x' -> V' x <=c V' x'.
  move => xe xe' lexy; case: (equal_or_not x x') => lxx.
    rewrite lxx; apply: (cleR (CS_nat (hf' _ xe'))).
  exact (proj1 (scV' _ _ xe xe' (conj lexy lxx))).
have iV': {inc E' &,injective V'}.
  move => x x' xE xE' /= sv.
  case: (NleT_ell (hb' _ xE)(hb' _ xE')) => // lxx. 
    by case: (proj2(scV' _ _ xE xE' lxx)).
    by case: (proj2(scV' _ _ xE' xE lxx)).
have ce': cardinal E' = q *c (n -c k). 
  move: (pP) => [qa3 qb'' qc'']. 
  move: (partition_nq_pr1 qa3); rewrite qb''. 
  move/Zo_S: qa3 => /partitionsP [[ <-]] //.
have np := (clt_leT kp lkn).
have cN:= (NS_prod qN (NS_diff k nN)).
have ax: lf_axiom V' E' T.
  move => t tE; apply /(NintP cN).
  set y := cpred (q *c n).
  have nnz := (nesym (proj2 np)).
  move:(cpred_pr qnN (cprod2_nz (nesym (proj2 qp)) nnz)) =>[yN yv].
  have lety: t <=c y by  move: (hb _ tE); rewrite yv; move/(cltSleP yN).  
  have yE1:=(cpred_lt qnN (cprod2_nz (nesym (proj2 qp)) nnz)).
  case: (inc_or_not y E') => yE.
    have sa:V' y <c q *c (n -c k).
      case (equal_or_not (V y ) k) => eyk.
        move: yE1. 
        rewrite -/y {1} (hf _ yE) eyk -{1} (cdiff_pr lkn) cprodDr => sa.
        exact: (csum_lt2l (NS_prod qN kN)(hf' _ yE) cN sa).
      exact:(clt_leT  (prop2 _ yE eyk) (jp10 _ (conj (ha _ yE) eyk))).
    exact:(cle_ltT (scV'' _ _ tE yE lety) sa).
  move:(Exercise5_9l7 nN qN qp lkn jP kN kp); rewrite - Ev; case.
    by move/yE.
  case.
    move => h;apply: (cle_ltT (cdiff_ab_le_a  _ (proj31 lety))  (h t tE)). 
  move => [j [ja jb jc jd je]].
  have jN:= (NS_lt_nat ja kN).
  have x'N := NS_prod qN (NS_sum (NS_diff k nN) jN).
  set x' := (q *c ((n -c k) +c j)) in ja jb jc jd x'N. 
  move: (cpred_pr x'N jb) => [xN xv].
  apply: (cle_ltT (scV'' _ _ tE jd (je _ tE))).
  apply/(cdiff_Mlt cN xN (he _ jd))/(cleSltP xN). 
  rewrite -xv {1} /x' cprodDr; apply:csum_Meqle; apply:cprod_Meqle. 
  case: (equal_or_not j \0c) => jnz.
    rewrite jnz; exact:(cle0x (proj31 (ha _ jd))).
  move: (cpred_pr jN jnz) => [ua ub].
  have uc: cpred j <c j by rewrite {2} ub; fprops.
  have la : (cpred x') <=c e j by rewrite /e jc {2} xv; fprops.
  have: e (cpred j) <c e j by apply: jp1.
  have cpjJ :=(jp4 _(clt_ltT uc ja)).
  rewrite {2} /e jc {1} xv; move/(cltSleP xN); case/cle_eqVlt => lb.
    by case: (qa'' _ _ jd); rewrite - lb.
  rewrite -(Exercise5_9l6bis jP kN kp xN ja jnz lb la). apply:cleR.
  exact:(proj31 (ra (cpred x'))).
have bo : bijection_prop (Lf V' E' T) E' T.
  saw.
  have fse:finite_set E' by apply /NatP; rewrite ce'.
  have ce'': cardinal E' = cardinal T by rewrite card_Nint.
  apply:bijective_if_same_finite_c_inj; aw; trivial; apply:lf_injective => //.
have iso:order_isomorphism (Lf V' E' T) (graph_on cardinal_le E')
     (graph_on cardinal_le T).
   have sa: cardinal_set E' by move => t /hb' /CS_nat.
   move: (wordering_cle_pr sa) => [[or1 _] sr1].
   have sb: cardinal_set T by move => t /Nint_S1 /CS_nat.
   move: (wordering_cle_pr sb) => [[or2 _] sr2].
   clear sa sb; hnf; rewrite sr1 sr2; split => //.
   hnf; aw => x y xe ye; rewrite ! LfV//; move: (ax _ xe) (ax _ ye) => xt yt.
   split;move/graph_on_P1 => [_ _ lta]; apply/graph_on_P1; split => //.
     by apply: scV''.
   by case:(NleT_el (hb' _ xe)(hb' _ ye)) => // /(scV' _ _ ye xe) /(cleNgt lta).
done.
Qed.


(* tentative 
Lemma Exercise5_9l8 q n k J p (E':= union p) (e := nth_elt J)
  (e':= fun i => e i -c q *c i) (V:=  Ex59_pos_in_J J k)
  (V' := fun x => x -c  q *c (V x))
  (T:= Nint (q *c (n -c k))):
  natp n -> natp q -> \0c <c q -> k <=c n ->
  Ex59_Jprop q n k J -> natp k -> \0c <c k ->
  Ex59_Cprop n q J k p ->
  [/\ 
    [/\ forall x, inc x E' -> V x = k -> e'(k -c \1c) +c q *c k <=c x,
    forall x, inc x E' -> \0c <c (V x) -> (V x) <c k -> 
     e'( (V x) -c \1c) +c q *c (V x) <=c x /\ x <c  e'(V x) +c q *c (V x),
    forall x, inc x E' ->  q *c (V x) <=c x & 
   forall x, inc x E' ->  x =  q *c (V x) +c V' x],
  order_isomorphism (Lf V' E' T) (graph_on cardinal_le E')
     (graph_on cardinal_le T) &
   inc (extension_p3 (Lf V' E' T) p) (Ex59_k_interval T q \0c)].


have res1:inc (extension_p3 (Lf V' E' T) p) (Ex59_k_interval T q \0c).
  move: pP  => [pp1 pp2 pp3]. rewrite - Ev in pp1.
  apply: (Zo_i (partition_nq_pr6c bo pp1));rewrite /Ex59_nb_int. 
  set T1 := Zo _ _; suff: T1 = emptyset by move ->; rewrite cardinal_set0.
  have pp: inc p (\Po(\Po E')) by move/Zo_S:pp1 => /Zo_S.
  apply/set0_P => x /Zo_P[ /(ext2_pr3 bo pp) [u up uv] [j jN xv]].

*)


Definition Ex59_no_int n q := cardinal (Ex59_k_interval (Nint (q *c n)) q \0c).

(** -- *)

(** Exercise 5.10 *)

Lemma even_compare n p: 
  natp p -> evenp n -> n <=c (\2c *c p) +c \1c -> n <=c (\2c *c p).
Proof.
move => pa pb; rewrite (half_even pb); set m :=  (n %/c \2c).
move: pb => [pc pd]; move:  (NS_quo \2c pc) => mB.
case: (cleT_el (CS_nat mB) (CS_nat pa)) => le1 le2.
   exact (cprod_Mlele (cleR CS2) le1).
move /(cleSltP pa): le1 => le3. 
have aux: natp (\2c *c p +c \1c) by fprops.
move: (cprod_Mlele (cleR CS2) le3); rewrite (Nsucc_rw pa).
rewrite cprodDr - (csum_nn \1c) csumA - (Nsucc_rw aux).
by move /(cleSltP aux) => /(cleNgt le2).
Qed.

Lemma cardinal_set_of_increasing_functions5 p n:
  natp p -> natp n ->
  cardinal(functions_incr (Nint_cco \1c p)(Nint_cco \0c n)) =
  binom (n +c p) p.
Proof.
move => pN nN.
move:  (Ninto_wor \1c p) (Ninto_wor \0c n)=> [a1 a2][a3 a4].
move: (worder_total a1) (worder_total a3).
set r := (Nint_cco \1c p); set r' := (Nint_cco \0c n) => pa pb.
move: (card_Nint1c pN);rewrite /Nint1c - a2.
rewrite -/r => r1.
have pc: finite_set (substrate r) by apply /NatP; rewrite r1.
move: (card_Nintc nN);rewrite /Nintc - a4.
rewrite -/r' => r2.
have pd: finite_set (substrate r') by apply /NatP; rewrite r2; fprops.
move: (cardinal_set_of_increasing_functions4 pa pb pc pd).
rewrite r1 r2 (csum_Sn _ nN) (Nsucc_rw (NS_sum nN pN)).
by rewrite (cdiff_pr1 (NS_sum nN pN) NS1).  
Qed.


Lemma Exercise5_10 n k
    (o1 := Nint_cco \1c k) (o2 := Nint_cco \1c n)
    (even_odd_fct := fun f =>
       (forall x, inc x (source f) -> evenp x -> evenp (Vf f x))
       /\ (forall x, inc x (source f) -> oddp x -> oddp (Vf f x))):
   natp n -> natp k ->
   cardinal (Zo (functions_sincr o1 o2) even_odd_fct) =
   binom  ((n +c k) %/c \2c) k.
Proof.
move: NS0 => ns0 nN kN; set A := Zo _ _.
set I1:= Nint1c k; set I2:= Nint1c n.
move: (proj2 (Ninto_wor \1c n)); rewrite -/o2 -/(Nint1c n) -/I2 => sr2.
move: (proj2 (Ninto_wor \1c k)); rewrite -/o1 -/(Nint1c k) -/I1  => sr1.
pose EF f z := Yo (z = \0c) \0c (Vf f z).
move: (NS_succ  kN); set sk := csucc k; move => skN.
have pa: forall f, inc f A -> forall i, i <> \0c -> i <c sk -> inc i (source f).
   move => f /Zo_P [] /Zo_P [] /functionsP [ff sf tf] _ _ i inz ik.
   rewrite sf sr1; apply /(Nint1cP kN); split => //. 
   by apply /(cltSleP kN).
have pa': forall f, inc f A -> forall i, 
    inc i (source f) -> i <> \0c  /\ i <c sk.
   move => f /Zo_P [] /Zo_P [] /functionsP [ff sf tf] _ _ i.
   rewrite sf sr1; move /(Nint1cP kN) => [p1 p2];split => //.
   by apply /(cltSleP kN).
have pb: forall f, inc f A -> (forall i, i <c sk -> natp (EF f i)).
   move => f fa; move: (fa) => /Zo_P [] /Zo_P [] /functionsP [ff sf tf] _ _.
   move => i ik; rewrite /EF; Ytac iz; [fprops | move: (pa _ fa _ iz ik)=> isf].
   move: (Vf_target ff isf); rewrite tf sr2; apply: (Nint_S). 
have pc: forall f, inc f A -> (forall i j, i <c j -> j <c sk ->
     (EF f i) <c (EF f j)).
   move => f fa i j ij jsk.
   have jnz: j <> \0c by move => jz; case: (clt0 (x := i)); ue.
   move: (pa _ fa _ jnz jsk) => jsf.
   move: (fa) => /Zo_P []  /Zo_P [p1 [p2 p3 [p4 p5 p6] p7]] _.
   move: (pb _ fa _ jsk);rewrite /EF; Ytac0 => p8; Ytac iz.
      apply /strict_pos_P1 => //; move: (Vf_target p4 jsf). 
      by rewrite p6 sr2; move /(Nint1cP nN) => [].
  move: ij => [lij nij].
  move: (pa _ fa _ iz (cle_ltT lij jsk)) jsf; rewrite p5 sr1 => qa qb.
  have aux: glt o1 i j by split => //; apply /Ninto_gleP.
  by move: (p7 _ _ aux) => [] /Ninto_gleP [_ _ aa] bb; split.
have pd: forall f, inc f A -> forall x, inc x (source f) -> x <=c Vf f x.
  move => f fA.
  move: (strict_increasing_prop1 skN (pb f fA) (pc f fA)) => h x xsf.
  by move: (pa' _ fA _ xsf) => [p1 p2]; move: (h _ p2); rewrite /EF; Ytac0.
case: (NleT_el kN nN) => lekn; last first.
  have -> : A = emptyset.
    apply /set0_P => f fA. 
    move /Zo_P: (fA) => [] /Zo_P [] /functionsP [ff sf tf] _ _.
    have ksf: inc k (source f).
       rewrite sf sr1; apply /Nint1cP => //;split;fprops => kz.
       by case: (clt0 (x := n)); rewrite - kz.
    move: (Vf_target ff ksf); rewrite tf sr2; move/(Nint1cP nN) => [_ H].
    case: (cltNge lekn (cleT (pd _ fA _ ksf) H)).
  rewrite cardinal_set0 binom_bad //; first by fprops.
  move: (csum_Mlteq kN lekn) => lt1.
  move: (cdivision (NS_sum nN kN) NS2 card2_nz).
    set q := ((n +c k) %/c \2c); set r := ((n +c k) %%c \2c).
    move => [s1 s2 [s3 s4]].
  apply: (cprod_lt2l NS2 s1 kN). 
  rewrite -(csum_nn k); apply: cle_ltT lt1; rewrite s3.
  apply: (Nsum_M0le r (NS_prod NS2 s1)). 
move: (NS_diff k nN)  => nkN.
move:  (cdivision nkN NS2 card2_nz).
set p := (n -c k) %/c \2c; set r := ((n -c k) %%c \2c).
move => [pN rN [p1 p2]].
have ->: (n +c k) %/c \2c = p +c k.
   have aux:cdivision_prop (n +c k) \2c (p +c k) r.
     split; last by exact.
     rewrite (csumC p) cprodDr - csumA - p1 -(csum_nn k) - csumA.
     by rewrite  (cdiff_pr lekn) csumC.
   by rewrite (proj1 (cquorem_pr (NS_sum nN kN) NS2 (NS_sum pN kN) rN aux)).
pose EG f x := ((Vf f x) -c x) %/c \2c.
rewrite -(cardinal_set_of_increasing_functions5 kN pN).
set o3:= Nint_cco \0c p; rewrite -/o1.
set I3 := Nintc p.
have sr3: substrate o3 = I3 by apply: (proj2 (Ninto_wor \0c p)).
set B := functions_incr o1 o3.
apply /card_eqP.
exists (Lf (fun f => (Lf (EG f) I1 I3)) A B); saw.
have pe: forall f, inc f A -> 
      [/\ (forall x, inc x (source f) -> Vf f x = x +c \2c *c (EG f x)),
       lf_axiom (EG f) I1 I3 &
       inc (Lf (EG f) I1 I3) B].
  move => f fA.
  move : (fA) => /Zo_P [] /Zo_P [] /functionsP [ff sf tf] ff1 ff2. 
  have qa: (forall i : Set, i <c sk -> EF f i <c (n -c k) +c sk).
    move =>i isk; rewrite /sk (csum_nS _ kN) csumC (cdiff_pr lekn).
    apply /(cltSleP nN); rewrite /EF; Ytac zi; first apply: (cle0n nN).
    move: (pa _ fA _ zi isk) => isf.
    by move: (Vf_target ff isf); rewrite tf sr2; move/(Nint1cP nN) => [].
  have qb:(forall x, inc x (source f) -> (Vf f x) -c x <=c n -c k).
  move: (strict_increasing_prop3 skN  (pb f fA) (pc f fA) nkN qa) => h.
    move => x xsf.
    by move: (pa' _ fA _ xsf) => [p4 p5]; move: (h _ p5); rewrite /EF; Ytac0.
  have qc:  forall x, inc x (source f) -> natp (Vf f x -c x).
     move => x xsf; exact: (NS_le_nat (qb _ xsf) nkN).
  have qd:  forall x, inc x (source f) ->x +c (Vf f x -c x) = Vf f x.
     move => x xsf; exact(cdiff_pr (pd _ fA _ xsf)).
  have qe: forall x, inc x (source f) -> evenp  ((Vf f x) -c x).
    move => x xsf; move:(qd _ xsf) => h; move:(qc _ xsf) => dN.
    have xN: natp x by move: xsf; rewrite sf sr1; apply: Nint_S.
    ex_middle od; have oi: oddp  (Vf f x -c x) by split.
    case: (p_or_not_p (evenp x)) => evx.
      move: (proj1 ff2 x xsf evx) => evf.
      by move: (csum_of_even_odd evx oi); rewrite h ; move => [].
    have oix: oddp x by split.
    move: (proj2 ff2 x xsf oix) => [_ evf].
    by move: (csum_of_odd oix oi); rewrite h.
  have qf: forall x, inc x (source f) -> Vf f x = x +c \2c *c (EG f x).
    by move => x xsf; rewrite - (qd _ xsf) (half_even (qe _ xsf)).
  have qg: forall x, inc x (source f) -> natp (EG f x).
    by move => x xsf; apply: (NS_quo); apply: qc.
  have qh: forall x, inc x I1 -> inc (EG f x) I3.
     rewrite - sr1 - sf => x xsf; suff: Vf f x -c x <=c \2c *c p.
       rewrite (half_even (qe _ xsf)) => h.
       apply /(NintcP pN).
       exact(cprod_le2l NS2 (qg _ xsf) pN card2_nz h).
    have aux: cardinalp (\2c *c p) by fprops.
    move: (qb _ xsf); rewrite p1; case: (clt2 p2) => ->; rewrite ? csum0r //.
    apply: (even_compare pN (qe _ xsf)).
  have qi: increasing_fun (Lf (EG f) I1 I3) o1 o3.
    red; aw; split => //. 
          by move: (Ninto_wor \1c k) => [[]].
        by move: (Ninto_wor \0c p) => [[]].
      by saw; try ue; apply: lf_function.
    move => i j /Ninto_gleP [iI jI ij]; rewrite !LfV//; apply/Ninto_gleP; split => //.
        by apply: qh.
      by apply: qh.
    have isf: inc i (source f) by rewrite sf sr1.
    have jsf: inc j (source f) by rewrite sf sr1.
    move: (pa' _ fA _ isf) (pa' _ fA _ jsf) => [s1 s2][s3 s4].
    move: (strict_increasing_prop2 skN (pb f fA) (pc _ fA) ij s4).
    rewrite /EF; Ytac0; Ytac0.
    rewrite  (half_even (qe _ isf)) (half_even (qe _ jsf)).
    apply: (cprod_le2l NS2 (qg _ isf) (qg _ jsf) card2_nz).
  split; [exact | exact | apply /Zo_P;split => //;apply/functionsP;red;aw].
  move: qi => [_ _[fh _ _] _]; split => //.
apply: lf_bijective.
    by move => f fA;move: (pe _ fA) => [_ _].
  move => u v uA vA sv; move: (pe _ uA) (pe _ vA) => [a1 e1 _][a2 e2 _].
  move /Zo_P: uA => [] /Zo_P [] /functionsP [u1 u2 u3] _ _.
  move /Zo_P: vA => [] /Zo_P [] /functionsP [v1 v2 v3] _ _.
  apply: function_exten => //; try ue.
  move => i isu /=; rewrite (a1 _ isu).
  rewrite u2 - v2 in isu; rewrite (a2 _ isu); congr (_ +c (_ *c _)).
  rewrite v2 sr1 in isu;  move: (f_equal (Vf^~ i) sv).
  by rewrite !LfV.
move => y /Zo_P [] /functionsP [fy sy tg] incy.
set f := Lf (fun i => i +c \2c *c (Vf y i)) I1 I2.
have qa: lf_axiom (fun i : Set => i +c \2c *c Vf y i) I1 I2.
  move => i i1; move: (i1) => /(Nint1cP kN) [qa qb]. 
  apply /(Nint1cP nN); split.
    move: (cpred_pr (NS_le_nat qb kN) qa) => [sa sb].
    rewrite {1}  sb (csum_Sn _ sa); apply: succ_nz.
  rewrite - (cdiff_pr lekn); apply: (csum_Mlele qb); rewrite p1.
  apply: cleT (Nsum_M0le r (NS_prod NS2 pN)).
  apply: (cprod_Mlele (cleR CS2)); apply /(NintcP pN).
  by rewrite -/I3- sr3 -tg; Wtac; rewrite sy sr1.
have ff: function f by apply: lf_function.
have eof: even_odd_fct f.
   have aux: forall x, inc x I1 -> evenp (\2c *c Vf y x).
      move => x x1; apply: even_double.
      have aux: inc (Vf y x) I3 by rewrite - sr3 - tg; Wtac; rewrite sy sr1.
      apply: (Nint_S aux).
   red; rewrite /f; aw; split => x xsf; rewrite LfV// => ex.
       exact: (csum_of_even ex (aux _ xsf)).
   rewrite csumC; exact (csum_of_even_odd (aux _ xsf) ex).
have fa: inc f A.
  apply /Zo_P; split; last by exact.
  apply /Zo_P; split; first by rewrite/f; apply /functionsP;red;saw.
  rewrite /f; red;split;aw;trivial.
          by move: (Ninto_wor \1c k) => [[]].
        by move: (Ninto_wor \1c n) => [[]].
      by saw.
    move: incy => [_ _ _ s6].
    move => i j [] q1; move: (s6 _ _ q1) =>  /Ninto_gleP [a1 a2 q7].
    move /Ninto_gleP: q1 =>  [q1 q2 q3] q4; rewrite !LfV//.
    have [q5 q6]: i +c \2c *c Vf y i <c j +c \2c *c Vf y j.
      move: (NS_prod NS2 (Nint_S a1)) (NS_prod NS2 (Nint_S a2)) => a3 a4.
      rewrite (csumC i) (csumC j); move: (cprod_Mlele (cleR CS2) q7) => q8.
      apply: (csum_Mlelt  a4  q8 (conj q3 q4)).
    split; [apply /Ninto_gleP;split => //; by apply: qa | done ].
exists f => //.
move: (pe _ fa) => [sa sb sc].
symmetry;apply: function_exten; aw; trivial;try ue; first by apply: lf_function.
move => i iI1 /=; aw; rewrite /EG /f /=; rewrite LfV// LfV//.
have aux: inc (Vf y i) I3 by rewrite - sr3 - tg; Wtac; rewrite sy sr1.
have iB: natp i by apply: (Nint_S iI1).
have fiB: natp (Vf y i) by apply: (Nint_S aux).
rewrite csumC (cdiff_pr1 (NS_prod NS2 fiB) iB).
apply: (cdivides_pr4 NS2 fiB card2_nz).
Qed.

(* ------------------------------------------------ *)

(** **  Section 6 *)
(** Exercise 6.1 *)

Lemma Exercise_6_1  E: infinite_set E <->
  (forall f, function_prop f E E ->
    exists S, [/\ sub S E, nonempty S, S <> E & sub (Vfs f S) S]).
Proof. 
split.
  move=> iE f [ff sf tf].
  case: (emptyset_dichot E) => [ ee | [y yE]].
    move/NatP: NS0; rewrite - cardinal_set0 - ee => fce.
    by case: (finite_not_infinite_set fce iE).
  have p1: (forall u, inc u E -> inc (Vf f u) E) by rewrite -{1} sf -tf; fprops.
  move:(induction_defined_pr (fun n  => Vf f n) y).
  move: (integer_induction_stable yE p1).
  set g:=induction_defined _ _; set (F:= target g).
  move=> stg [sg sjg g0 gs].
  have fg: function g by fct_tac.
  have yF: inc y F. rewrite -g0;apply: Vf_target => //; rewrite sg; apply:NS0.
  have sFf:sub F (source f) by ue.
  have fF: (sub (Vfs f F) F). 
    move=> t /(Vf_image_P ff sFf) [u uF ->]. 
    move: ((proj2 sjg) _  uF); rewrite sg; move => [n ns ->].
    by rewrite -gs//;apply:Vf_target;[ fct_tac |rewrite sg; apply: NS_succ].
  set (G:=Vfs f F). 
  have sgg: sub (Vfs f G) G.
    have aux:sub (Vfs f F) (source f) by apply: (@sub_trans F).
    move=> t /(Vf_image_P ff aux) [u ui ->]; apply /(Vf_image_P ff sFf).
    exists u;fprops.
  exists G; split => //; first by  apply: (@sub_trans F) =>//. 
     exists (Vf f y);  apply /(Vf_image_P ff sFf); ex_tac. 
  move=> GE; move: yE; rewrite -GE;move=> /(Vf_image_P ff sFf)[u uF Wu].
  move: ((proj2 sjg) _ uF) => [x0 x0g Wx].
  rewrite sg in x0g; move: Wu; rewrite Wx -gs //.
  set (k:=  csucc x0). 
  move=> Wy. 
  have kN: natp k by apply: NS_succ.  
  have rec1: (forall i, natp i ->  Vf g i = Vf g (i +c k)).
    have ck: cardinalp k by fprops.
    apply: Nat_induction; first by rewrite csum0l //g0 Wy.  
    move => n nN; rewrite (gs _ nN)  (csumC (csucc n) _) csum_nS //.
    move ->; rewrite csumC gs //; fprops.
  have rec2: (forall i, natp i -> forall j, natp j ->  
     Vf g i = Vf g (i +c (j *c k))). 
    move => i iN; apply: Nat_induction. 
      rewrite cprodC cprod0r csum0r //; fprops. 
    move=> n nN; rewrite (cprodC (csucc n) _) cprod_nS // csumA.
    rewrite cprodC -rec1 //; fprops.
  have rec4: (forall z, inc z E -> exists2 m,  m <c k & z = Vf g m). 
    move=> z; rewrite -GE;move=> /(Vf_image_P ff sFf) [w w1 w2]. 
    move: ((proj2 sjg) _ w1) => [x xsg w3].
    rewrite sg in xsg;move: w2; rewrite w3 -gs //; move => ->.
    have sxN: (natp (csucc x)) by fprops. 
    have knz: (k <> \0c) by apply: succ_nz.
    move: (cdivision sxN kN knz) => [qN rN [pa pb]].
    rewrite pa; exists (csucc x %%c k) => //; rewrite csumC cprodC -rec2 //.
  have sisg: sub k (source g) by  rewrite sg; apply: (NS_inc_nat kN).
  have sEi: (sub E (Vfs g k)).
    move=> t tE; move: (rec4 _ tE) => [m /(NltP kN) ml ->].
    apply /(Vf_image_P fg sisg); ex_tac.
  have fsi: (finite_set k) by apply: finite_set_nat.
  move: (finite_image_by fg  fsi) =>  fs2.
  move: (sub_finite_set sEi fs2) => fs3.
  case: (finite_not_infinite_set fs3 iE).
move=> h; case: (finite_or_infinite_set E) => //.
rewrite /finite_set; set (n:= cardinal E); move /NatP => nN.
have:(n \Eq E) by apply /card_eqP; rewrite /n double_cardinal.
move=> [y [bjy sy ty]].
case: (emptyset_dichot E) => neE.
  have fpi: (function_prop (identity E) E E).
     saw; apply: identity_f. 
  move: (h _ fpi) => [F [FE [t tF] _]];empty_tac1 t.
have nz: n <> \0c by apply: card_nonempty1.
set (f:= fun i => (csucc i) %%c n).
have Ha: forall i, natp i -> inc (i %%c n) n.
  by move=> i iN; apply /(NltP nN); move: (cdivision iN nN nz) => [_ _ [_]].
have Hb:sub n Nat by apply:(NS_inc_nat nN).
have Hc:(forall i, inc i n -> inc (f i) n).
  by move=> i iI; apply: Ha; apply: NS_succ; apply: Hb.
move: (inverse_bij_fb bjy).
move: (ifun_s y) (ifun_t y).
rewrite sy ty;set x := (inverse_fun y) => sx tx bx.
have fx: function x by fct_tac.
have fy: function y by fct_tac.
set (g:= fun u => Vf y (f (Vf x u))). 
have ta: (lf_axiom g E E). 
  rewrite /g -{1} sx -ty; move=> t tsx /=; apply: Vf_target =>//.
  rewrite sy;apply: Hc; rewrite  -tx; Wtac.
set (g1:= Lf g E E). 
have fg1: (function g1) by apply: lf_function.
have fpg1: function_prop g1 E E by split => //; rewrite /g1; aw.
move: (h _ fpg1) => [F [FE [u uF] nFE Fsg]].
set (i:= Vf x u). 
have iin: inc i n by  rewrite/i; Wtac; rewrite sx; apply: FE.
have iN:= (Hb i iin).
have WiF: inc (Vf y i) F. 
  rewrite /i; move: (FE _ uF); rewrite -ty => uty.
  by rewrite  (inverse_V bjy uty).
have Hd: (forall j, natp j -> inc (Vf y ( (i +c j) %%c n)) F).
  apply: Nat_induction.
    rewrite Nsum0r //.
     have dp:(cdivision_prop i n \0c i).
       split; first by rewrite cprod0r Nsum0l //.
       by apply /(NltP nN).
     by move: (cquorem_pr iN nN NS0 iN dp) => [_ ] <-.
  move => m mN.
  have imN: natp (i +c m) by fprops.
  set (v:= (i +c m) %%c n) => WvF.
  have vN: natp v by rewrite /v; fprops.
  have : (inc (Vf g1 (Vf y v)) F). 
    have aux: sub F (source g1) by rewrite /g1;aw.
    apply: Fsg; apply /(Vf_image_P fg1 aux); ex_tac.
  rewrite /g1 LfV//; last (by apply: (FE _ WvF)); rewrite /g.
  move: (Ha _ (NS_sum iN mN)); rewrite  - {2} sy -/v => vs.
  rewrite (inverse_V2 bjy vs). 
  have <-: ((csucc v) %%c n = (i +c (csucc m)) %%c n) => //.
  rewrite -/(eqmod _ _ n)  (csum_nS _ mN); apply: (eqmod_succ nN nz vN imN).
  by rewrite /v /eqmod; symmetry; apply: eqmod_rem.
case: nFE; apply: extensionality => //. 
rewrite -ty; move=> t tE.
move: (bjy) => [_ sjy].
move: ((proj2 sjy) _ tE) => [v vsy ->]. 
move: vsy; rewrite sy =>  /(NltP nN) vn.
move: iin => /(NltP nN) [lein _].
move: (f_equal (fun  z => (z +c v)) (cdiff_pr lein)).
move: (vn) => [len _ ]; move: (NS_le_nat len nN) =>  vB.
rewrite - csumA;  set k:=  _ +c v => aux.
have kb: natp k by rewrite /k; fprops.
have dp:(cdivision_prop (i +c k) n \1c v) by split=> //; rewrite cprod1r;fprops.
move: (cquorem_pr (NS_sum iN kb) nN NS1 vB dp) => [_ ] ->.
by apply: Hd.
Qed.


Fixpoint chain_val x :=
  match x with chain_pair u v => singleton u
    | chain_next u v => chain_val v +s1 u
 end.

Fixpoint sub_chain x y :=
  match y with 
    chain_pair u v => x = y
   | chain_next u v => 
     x = y \/ sub_chain x v
end.

Lemma sub_chainedP R p q: sub_chain p q -> chained_r R q ->
     chained_r R p /\ chain_tail p = chain_tail q.
Proof.
move => p1 p2; split.
  move: p1 p2; elim q => a x /=; first by move => -> /=.
  move => Hrec; case => aux; first by rewrite aux /= => [].
  by move => [p1 p2]; apply: Hrec.
clear p2; move: p1; elim: q => a x /=; first by move => -> /=.
move => Hrec; case => aux; [ by rewrite aux | by  apply: Hrec].
Qed.

Lemma chained_prop1 g a c: 
  chained_r (fun a b => a = g b) c -> chain_tail c = a -> 
      sub_chain (chain_pair (g a) a) c.
Proof.  
elim:c => b x /=; first by move => -> ->.
by move => Hrec [p1 p2] p3; right; apply: Hrec.
Qed.

Lemma chained_prop2 g p c: 
  chained_r (fun a b => a = g b) c -> sub_chain p c ->
   p = c \/ sub_chain (chain_next (g (chain_head p)) p) c.
Proof.
elim:c => a c /=; first by left.
move => Hrec [p1 p2]; case => p3; first by left.
case: (Hrec p2 p3); last by right; right.
by move => epc; right; left; rewrite epc -p1.
Qed.

Lemma chain_valP x i: inc i (chain_val x) <->
  (exists2 p, sub_chain p x & i = chain_head p).
Proof.
split.
  elim:x => a x /=.
    by move /set1_P ->; exists (chain_pair a x).
  move => Hrec /setU1_P; case => aux.
    by move: (Hrec aux) => [p p1 p2]; exists p => //; right.
   by exists (chain_next a x) => //; left.
move => [p].
elim: x => a x /=; first by move => -> -> /=; fprops.
move => Hrec p1 p2; case: p1; first by rewrite p2; move => -> /=; fprops.
by move => p3; apply /setU1_P; left; apply: Hrec. 
Qed.

Lemma chain_val_finite x: finite_set (chain_val x).
Proof.
elim: x => [pa pb /=| pa pb /= Hrec]; first by apply: set1_finite.
by apply: setU1_finite.
Qed.

Lemma Exercise_6_1bis E f: infinite_set E -> function_prop f E E ->
    exists S, [/\ sub S E, nonempty S, S <> E & sub (Vfs f S) S].
Proof. 
move => /infinite_setP pa [pb pc pd]; pose g x := Vf f x.
have qa: forall x, inc x E -> inc (g x) E.
   move => x; rewrite - {1} pc -  pd /g => xsf; Wtac.
case: (emptyset_dichot E).
  move => ee; rewrite ee in pa. 
  have fce: finite_c (cardinal emptyset) by rewrite cardinal_set0; fprops.
  case: (finite_not_infinite fce pa).
move=> [y0 y0E]; pose y := g y0.
have yE: inc y E by apply: qa.
pose stable S := forall x, inc x S -> inc (g x) S.
pose chained := chained_r (fun a b => a = g b).
set S := Zo E (fun z => exists p, [/\ chained p, chain_tail p = y0 &
   (chain_head p) = z]).
have q0: forall p, chained p -> chain_tail p = y0 -> inc (chain_head p) E.
   elim => c p //= ; [ by move => -> -> | move => Hrec [] -> rb rc].
   by apply:qa; apply: Hrec.
have q1: sub S E by apply: Zo_S.
have q2: nonempty S by exists y; apply/Zo_i => //; exists (chain_pair y y0). 
have q3: stable S.
   move => t /Zo_P [tE [c [c1 c2 c3]]]; apply/Zo_P; split => //. 
       by apply: qa. 
   by exists (chain_next (g t) c);split => //; rewrite - c3.
have q4:forall S, sub S E -> stable S -> sub (Vfs f S) S.
   move => s se ss.
   have aux: sub s (source f) by ue.
   by move => t /(Vf_image_P pb aux) [u us ->]; apply: ss.
case: (equal_or_not S E) => nse; last by exists S;split;fprops.
have: inc y0 S by ue.
move /Zo_P => [_] [c0 [c1 c2 c3]].
set A:= chain_val c0.
have yA: inc y A.
  by apply /chain_valP; exists (chain_pair y y0) => //;apply chained_prop1.
have sa: stable A.
  move => s /chain_valP [p p1 ->]; case: (chained_prop2 c1 p1) => sq.
  rewrite sq c3; exact yA.
  by apply /chain_valP; exists (chain_next (g (chain_head p)) p).
have sas: sub A E.
  move => t /chain_valP [p p1 p2].
  move: (sub_chainedP p1 c1); rewrite  c2 p2; move => [xx1 xx2].
  by apply: q0.
have ae: A <> E.
  move => bad.
  have : finite_set A by apply: chain_val_finite.
  by rewrite bad => fse; exact:(finite_not_infinite fse pa).
exists A;split => //; [ by exists y | by apply: q4].
Qed.

(** Exercise 6.2 *)

Lemma exercice6_2 a b c d: 
  a <c c -> b <c d -> ((a +c b) <c (c +c d) /\ (a *c b) <c (c *c d)).
Proof. 
move=> ac bd.
wlog: a b c d ac bd / ( c <=c d).
  move=> h.
  case: (cleT_ee (proj32_1 ac) (proj32_1 bd)) => aux.
    by apply: h.
  by rewrite csumC (csumC c _) cprodC (cprodC c _); apply: h.
move=> cd.
have cnz: c <> \0c. 
   move=> cz; rewrite cz in ac; exact: (clt0 ac).
have cad:= proj32 cd.
case: (finite_or_infinite cad) => fcd.
  move: ac => [ac _].
  have dN: natp d by apply /NatP.
  have bN:= NS_lt_nat bd dN.
  have cN:= NS_le_nat cd dN.
  have aN:= NS_le_nat ac cN.
  split; [ apply: csum_Mlelt => // | apply: cprod_Mlelt  => //].
rewrite (cprodC c d) (csumC c d). 
rewrite (cprod_inf cd fcd cnz) (csum_inf cd fcd).
have caa:= proj31_1 ac.
have cab:= proj31_1 bd. 
have fcz:= finite_0.  
wlog : / (infinite_c b /\ a <=c b); last first.
  move=> [fcb leab].
  split; first by rewrite  csumC (csum_inf leab fcb).
  rewrite cprodC; case: (equal_or_not a \0c) => az.
    by rewrite az cprod0r; apply: clt_fin_inf.
  by rewrite (cprod_inf leab fcb az).
move=> wwlog; case: (finite_or_infinite caa) => fca.
  case: (finite_or_infinite cab) => fcb.
    split; apply: clt_fin_inf => //; fprops.
  move: (cle_fin_inf fca fcb) => ab; apply: wwlog;split => //.
case: (cleT_ee caa cab) => ba.
  case: (finite_or_infinite cab) => fcb.
   case: (cleNgt ba (clt_fin_inf fcb fca)).
  apply: wwlog;split => //. 
have ltad:= clt_leT ac cd.
split; first by rewrite (csum_inf ba fca).
case: (equal_or_not b \0c) => bz.
  by rewrite bz cprod0r; apply: clt_fin_inf.
by rewrite (cprod_inf ba fca bz).
Qed.

(** -- Exercise 6.3 *)

Lemma Exercise6_3 E: infinite_set E ->
  (\Po E) \Eq  (Zo (\Po E) (fun z => z \Eq E)).
Proof. 
move=> isE; set Qo:= Zo _ _.
apply /card_eqP;apply: cleA; last first.
  have sQ: (sub Qo (\Po E)) by apply: Zo_S.
  apply: (sub_smaller sQ).  
set (n:= cardinal E). 
have cnn: (n +c n = n).
  have cnn: (n <=c n) by rewrite /n; fprops. 
  move: isE => /infinite_setP isE.
  apply: (csum_inf cnn isE).
have enE: n =c E by rewrite /n; aw.
set (E1:= E *s1 C0); set(E2:= E *s1 C1).
have d12: (disjoint E1 E2) by  apply: disjointU2_pr; fprops. 
move: (csum2_pr5 d12); rewrite - csum2cl - csum2cr.
rewrite !cardinal_indexed  cnn; move /card_eqP => [g [bg sg tg]].
have fg: function g by fct_tac.
pose barX X:= ((X *s1 C0) \cup E2).
pose f X := Vfs g (barX X).
have barXp: forall X, sub X E -> sub (barX X) (source g).
  move => X XE s; rewrite sg; case /setU2_P => //; last by fprops.
    move/indexed_P=> [ps PX Qs]; apply /setU2_P;left; apply /indexed_P; aw. 
    by split => //; apply XE.
have sfE:(forall X, sub X E -> sub (f X) E). 
   move=> X XE t; move: (barXp _ XE) => bE; move /(Vf_image_P fg bE).
   rewrite -tg;move=> [u ub ->]; apply: Vf_target => //;apply: bE => //.
have ei: (forall X, sub X E -> (f X) \Eq E). 
  move=> X XE; move: (sfE _ XE) => ssfE.
  apply/card_eqP;apply: (cleA (sub_smaller ssfE)).
  have <-: (cardinal E2 = cardinal E) by exact: cardinal_indexed.
  have sE2: (sub E2 (source g)) by rewrite sg;apply:  subsetU2r.
  move: (bg) => [bg1 _]. 
  move/card_eqP: (Eq_restriction1 sE2 bg1) => ->. 
  apply:sub_smaller;apply: dirim_S; apply: subsetU2r.
have ta: (lf_axiom f (\Po E) Qo). 
  move => X /setP_P XE; apply: Zo_i;fprops;apply /setP_P; apply: sfE =>//.
set (F:=  Lf f (\Po E) Qo). 
have ->: (\Po E = source F) by rewrite /F; aw.
have ->: (Qo = target F) by rewrite /F; aw.
apply: inj_source_smaller.
apply: lf_injective => // a b /setP_P aE /setP_P bE; move: aE bE.
suff: forall u v, sub u E -> sub v E -> f u = f v -> sub u v.
  move=> h ae ve sf; apply: extensionality; apply: h => //.
move => u v uE vE sf t tu.
have p1: (inc (J t C0) (barX u)) by apply :setU2_1;apply :indexed_pi.
move: (barXp _ uE) => p2;  move: (barXp _ vE) => p2a; move: (p2 _ p1) => p3.
have :(inc (Vf g (J t C0)) (f u)) by apply/(Vf_image_P fg p2); ex_tac.
rewrite sf =>  /(Vf_image_P fg p2a) [w wb wv]; move: (p2a _ wb)=> wsg.
move: bg => [[_ ig] _]; move: (ig _ _ p3 wsg wv) => wv2.
move: wb; rewrite -  wv2 => /setU2_P; case; move /indexed_P => [_]; aw; trivial.
by move => _ bad; case: C0_ne_C1.
Qed.

(** -- Exercise 6.4 *)

Lemma card_powerset_rw x y: cardinal x = cardinal y ->
   cardinal (\Po x) = cardinal (\Po y). 
Proof. by move => eq; rewrite ! card_setP - cpowcr eq cpowcr. Qed.

Lemma Exercise6_4a E: infinite_set E ->
  cardinal (\Po (coarse E)) = cardinal (\Po E).
Proof.
move => /infinite_setP ife.
apply: (card_powerset_rw).  
by rewrite /coarse - cprod2_pr1 - cprod2cl  - cprod2cr csquare_inf.
Qed.

Lemma infinite_powerset E:
  infinite_set E -> infinite_set (\Po E).
Proof.
move=> /infinite_setP iE; move: (proj1 (cantor (CS_cardinal E))) => lt1.
apply/infinite_setP; rewrite card_setP - cpowcr. 
apply: (cle_inf_inf iE lt1).
Qed.

Lemma Exercise6_4 E: infinite_set E ->
   (partitions E) \Eq (\Po E). 
Proof. 
move=> ifE.
move/infinite_setP: (ifE) => ifE'.
set (q:=partitions E).
apply/card_eqP; apply: cleA.
  set (f:= Lf (fun y=> partition_relset y E) q (\Po (coarse E))).
  have injf: (injection f).
    apply: lf_injective.
      by move=> t tp;apply/setP_P; apply: sub_part_relsetX; move: tp =>/Zo_P [].
    move=> u v => /Zo_P [] /setP_P uE puE  /Zo_P [] /setP_P vE pvE sp.
    exact: (part_relset_anti puE pvE).
  by move: (inj_source_smaller injf); rewrite /f; aw; rewrite (Exercise6_4a ifE).
case: (emptyset_dichot E) => neE.
  by move/infinite_nz: (ifE'); rewrite neE cardinal_set0.
move: neE => [y yE].
set (F:= E -s1  y).
pose g u := doubleton u (E -s u).
have yF: ~(inc y F) by move /setC1_P => [].
have ig: (forall u v , sub u F -> sub v F -> g u = g v -> u = v). 
  rewrite /g;move=> u v uF vF sg; case: (doubleton_inj sg); first by case.
  move=> [uc vc].
  case: (yF); apply: uF; rewrite uc; apply /setC_P. 
  by split => // yv; move: (vF _ yv).
have pa: (forall u, sub u F -> nonempty u -> inc (g u) q).
  move=>  u uF neu.
  have uE: (sub u E) by apply: (@sub_trans F)=> //; apply: sub_setC. 
  rewrite /g;apply /partitionsP; split; last first.
    move=> a; case /set2_P;move => -> //; exists y; apply /setC_P;split;fprops.
  split; first by rewrite -/(_ \cup _) setU2_Cr.
  have dc: forall u, disjoint u (E -s u).
    by move => w; apply: disjoint_pr; move=> t tw; apply /setC_P; case.
  move=> a b; case/set2_P => p1; case /set2_P=> p2;
     rewrite ? p1 ?p2 /disjointVeq; fprops.
   right;apply: disjoint_S; apply: dc.
move: (card_setC1_inf y ifE); rewrite -/F => cEF.
have ipF: (infinite_set (\Po F)).
  by apply: infinite_powerset; apply /infinite_setP;rewrite - cEF.
rewrite (card_powerset_rw cEF) (card_setC1_inf emptyset ipF).
apply /eq_subset_cardP1.
exists (Lf g ((\Po F -s1 emptyset)) q); saw; apply: lf_injective.
  by move=> t /setC1_P [] /setP_P tF te;apply: pa => //;apply /nonemptyP.
by move=> u v /setC1_P [] /setP_P uf _ /setC1_P [] /setP_P vf _; apply: ig.
Qed.


(** -- Exercise 6.5 *)

Lemma Exercise6_5d E: infinite_set E ->
  (cardinal (derangements E)) <=c  (cardinal (\Po E)).
Proof.
move => h.
have : sub  (derangements E)  (permutations E) by apply: Zo_S.
move /sub_smaller => p1.
exact:(cleT p1 (Exercise6_5c h)).
Qed.

Lemma Exercice6_5e E F h:
   bijection h -> source h = E -> target h = F ->
   (forall f, inc f (derangements F) ->
    inc ((inverse_fun h) \co  (f \co h)) (derangements E)).
Proof.
move=> bh sh tg f /Zo_P [/Zo_P [/functionsP [ff sf tf] bf] nfx].
set g := _ \co _.
have co: f \coP h by split => //; [fct_tac | ue].
have b1: bijection (f \co h) by apply: compose_fb.
move: (inverse_bij_fb bh) => ihb.
have co1: (inverse_fun h) \coP (f \co h).
  split => //; try fct_tac; aw; ue.
have bg: bijection g by apply: compose_fb.
apply: Zo_i. 
  by apply: Zo_i => //; apply /functionsP;split => //;try fct_tac;rewrite /g;aw.
rewrite - sh /g;move => x xE; rewrite ! compfV//; last by aw.
set y:= (Vf f (Vf h x)) => eq1.
have pe: inc (Vf h x) (source f) by rewrite sf -tg; Wtac; fct_tac.
have pd: inc y (target h) by rewrite /y tg -tf; Wtac.
rewrite sf in pe; move: (nfx _ pe); rewrite -/y.
by move: (inverse_V bh pd);rewrite eq1; move => ->; case.
Qed.

Lemma Exercice6_5f E F: E =c F -> 
  (derangements E) =c (derangements F).
Proof.
move => /card_eqP [h [pa pb pc]]; symmetry;apply/card_eqP.
exists (Lf (fun f => ((inverse_fun h) \co  (f \co h))) 
   (derangements F) (derangements E)).
move: (inverse_bij_fb pa) => bh'.
saw; apply: lf_bijective.
    by apply: Exercice6_5e.
  move => u v /Zo_P [] /Zo_P [] /functionsP [p1 p2 p3] _ _.
  move => /Zo_P [] /Zo_P [] /functionsP [p4 p5 p6] _ _ eq.
  have q1: u \coP h by split => //; try fct_tac; ue.
  have q2: v \coP h by split => //; try fct_tac; ue.
  have q3: function (u \co h) by fct_tac.
  have q4: function (v \co h) by fct_tac.
  have q5: inverse_fun h \coP (u \co h) by  saw;try fct_tac; ue.
  have q6: inverse_fun h \coP (v \co h) by  saw;try fct_tac; ue.
  move: (compf_regr bh' q5 q6 eq) => eq1.
  by move: (compf_regl pa q1 q2 eq1).
move => y yE.
exists  (h \co (y \co (inverse_fun h))).
    have eq1:inverse_fun (inverse_fun h) = h by apply: ifun_involutive; fct_tac.
    by rewrite -{1} eq1; apply: (Exercice6_5e bh' _ _ yE); aw.
move: yE => /Zo_P [] /Zo_P [] /functionsP [pd pe pf] _ _.
have p1: (y \coP inverse_fun h)  by saw;try fct_tac; ue.
have p2: function (y \co inverse_fun h)  by fct_tac.
have p3: (h \coP (y \co inverse_fun h)) by  saw;try fct_tac; ue.
set z := (h \co (y \co inverse_fun h)).
have p4: function z by rewrite /z; fct_tac.
have p5: inverse_fun h \coP z by rewrite /z;saw;try fct_tac.
have p6: z \coP h by rewrite /z;saw;try fct_tac.
rewrite (compfA p5 p6) (compfA (composable_inv_f pa) p3)(bij_left_inverse pa).
have ->: (source h) = target (y \co inverse_fun h) by aw; rewrite pb pf.
rewrite (compf_id_l p2) - (compfA p1  (composable_inv_f pa)).
by rewrite (bij_left_inverse pa) pb -pe  (compf_id_r pd).
Qed.


Lemma Exercice6_5g E: singletonp E \/ nonempty (derangements E).
Proof.
have re: forall F, F =c E -> nonempty (derangements F) ->
   nonempty (derangements E).
   move => F /Exercice6_5f h /card_nonempty1. rewrite h => h1.
   case:(emptyset_dichot (derangements E)) => // h2.
   by case h1; rewrite h2 cardinal_set0.
case: (finite_or_infinite (CS_cardinal E)) => ie; last first.
  move /infinite_setP: (ie) => iE; right.
  pose f z := J (P z) (variant C0 C1 C0 (Q z)).
  pose f':= Lf f (E \times C2)(E \times C2).
  have h: (E \times C2) =c E. 
    apply: cprod_inf3 => //; first by exists C0; fprops.
    by apply: cle_fin_inf => //; apply: set2_finite.
  apply: (re _ h); exists f'.
  have pa: lf_axiom f (E \times C2) (E \times C2).
    move => x /setX_P [pa pb pc]; rewrite /f; apply: setXp_i=> //.
    rewrite /variant; Ytac s; fprops.
  have pb: forall x, inc x  (E \times C2) -> f (f x) = x.
    move => x /setX_P [qa qb qc]; rewrite /f/variant; aw.
    case: (equal_or_not (Q x) C0) => aux; Ytac0; Ytac0.
      by rewrite - aux qa.
    by case /set2_P: qc => // <-; rewrite qa.
  have pc: bijection (Lf f (E \times C2) (E \times C2)).
    apply: lf_bijective => //.
      by move => u v u1 v1 eq; rewrite -(pb _ u1) -(pb _ v1) eq.
    by move => y ys; move: (pa _ ys) => xs; ex_tac; rewrite  pb.
  rewrite /f';apply :Zo_i; first apply: Zo_i => //.
    apply /functionsP; red; saw; fct_tac.
  rewrite /f; move => x xi; rewrite LfV// => p; move: (f_equal Q p); aw.
  rewrite /variant; Ytac s; [rewrite s |]; fprops.
move/NatP: ie; set n:= cardinal E => nN.
case: (equal_or_not n \1c) => no; first by left; apply/ set_of_card_oneP.
right.
case: (equal_or_not n \0c) => nz.
  exists (identity E).
  have ->: E = emptyset by apply: card_nonempty; ue.
  apply: Zo_i; last by move => x /in_set0.
  apply: Zo_i; first by apply /functionsP; apply: identity_prop.
  apply: identity_fb.
apply: (re n); first by rewrite /n; aw. 
move: (cpred_pr nN nz) => [pb pc].
pose f x := Yo (x = cpred n) \0c (csucc x).
exists (Lf f n n).
have ta: forall i, inc i n -> inc (f i) n.
  move => m /(NltP nN) mn; apply/(NltP nN);rewrite pc.
  rewrite /f; Ytac mp; first by apply:succ_positive.
  by apply/cltSS;split => //; apply/(cltSleP pb); rewrite -pc.
have injf: surjection (Lf f n n).
  apply: lf_surjective => // y /(NltP nN) [yN yy].
  case: (equal_or_not y \0c) => yz.
    exists (cpred n); last by rewrite /f; Ytac0.
    apply/(NltP nN); rewrite {2} pc; apply: cltS; fprops.
  move: (cpred_pr (NS_le_nat yN nN) yz) => [pyN ysc].
  exists (cpred y); rewrite /f -?ysc.
    by apply /(NltP nN); rewrite - cleSltP // -ysc.
  by rewrite Y_false// => ss; case:yy;rewrite ysc pc ss.
apply: Zo_i;first apply: Zo_i;first by apply /functionsP;saw;fct_tac.
  apply: bijective_if_same_finite_c_surj; aww.
  by apply:finite_set_nat.
move => x xf; rewrite LfV// /f; Ytac xx.
  by move => aux; move: pc; rewrite -xx -aux succ_zero.
move/NatP:(NS_inc_nat nN xf); case/ finite_cP;fprops.
Qed.


Lemma Exercice6_5h E: infinite_set E ->
  (permutations E) =c (\Po E).
Proof.
move=> isE.
set s:= (permutations E).
apply: cleA.
  by apply: Exercise6_5c.
set aux:= ((\Po E) -s (fun_image E singleton)).
have ->: cardinal (\Po E) = cardinal aux.
  rewrite /aux; set A := \Po E; set B:= fun_image _ _.
  symmetry; apply:(infinite_compl (infinite_powerset isE)).
  have -> : cardinal B = cardinal E.
    symmetry; apply /card_eqP;exists (Lf singleton E B); saw.
    apply: lf_bijective.
        move => t tE; apply /funI_P; ex_tac.
      move=> u v _ _ ss;  have : inc  u (singleton v) by rewrite - ss; fprops.
      by move /set1_P.
   by move=> y /funI_P.
 rewrite card_setP - cpowcr; apply:cantor; fprops.
apply: surjective_cle.
exists (Lf (fun z => (E -s (fixpoints z))) s aux).
saw; apply: lf_surjective.
  move=> f  /Zo_P [] /functionsP [ff sf tf] bf.
  apply /setC_P;split => //; first  by  apply /setP_P => t /setC_P [].
  move /funI_P=> [z zE sc].
  move: (set1_1 z); rewrite - sc; move /setC_P => [_  ze]; case: ze.
  apply: Zo_i; first (by ue).  
  rewrite - sf in zE.
  case: (inc_or_not (Vf f z) (fixpoints f)). 
   move /Zo_P => [pa pb]; move: bf => [[_ injf] _]; apply: (injf _ _ pa zE pb).
  move: (Vf_target ff zE); rewrite tf; move=> pa pb.
  have : inc (Vf f z) (singleton z) by rewrite - sc; apply /setC_P;split => //.
  by move /set1_P.
move=> F /setC_P [] /setP_P FE /funI_P ns.
case: (Exercice6_5g F).
   move=> [u ysu]; case: ns; exists u => //; apply: FE; rewrite ysu; fprops.
move=> [f /Zo_P [/Zo_P [pa pb] pc]].
pose g x:= Yo (inc x F) (Vf f x) x.
move: pa pb => /functionsP [ff sf tf] [[_ fi] sjf]. 
have ta: lf_axiom g E E.
  rewrite /g;move=> x xE; simpl; Ytac xf =>//.  
  apply: FE; rewrite -tf; apply: Vf_target  => //; ue.
have bg: (bijection (Lf g E E)).
  apply: lf_bijective => //.
    move=> u v uE vE; rewrite /g; Ytac uf; Ytac vf.
      by apply: fi; ue.
      by move => eql; rewrite -eql in vf; case: vf; rewrite -tf; Wtac.
      by move => eql; rewrite eql in uf; case: uf; rewrite -tf; Wtac.
      by [].
  move=> y yE; case: (inc_or_not y F) => yF.
    rewrite -tf in yF; move: ((proj2 sjf) _ yF) => [x].
    by rewrite sf => xF ->; move: (FE _ xF) => xE; ex_tac; rewrite /g; Ytac0.
  by exists y => //; rewrite /g; Ytac0.
exists  (Lf g E E). 
  by apply: Zo_i => //; apply /functionsP; saw; fct_tac.
symmetry;set_extens t. 
   by move => /setC_P [tE] /Zo_P;aw;rewrite LfV// /g; Ytac tF => //; case.
move => tF; apply /setC_P;split => //; first by apply: FE. 
move  /Zo_P; rewrite lf_source; move=> [tE]; rewrite /g LfV//; Ytac0 => tfi.
by case: (pc _ tF).
Qed.

Lemma Exercice6_5i E: infinite_set E ->
   (derangements E) =c (\Po E).
Proof.
move=> isE.
set s:= (permutations E).
apply: cleA; first  by apply: Exercise6_5d.
set F := E \times C3.
have pa: F =c E.
  apply:  cprod_inf3 => //; first by exists C2; rewrite /C3; fprops.
  apply cle_fin_inf => //; last by apply /infinite_setP.
  apply: setU1_finite; apply: set2_finite.
rewrite -(Exercice6_5f pa). 
pose fa z := (Yo (z = C0) C1 (Yo (z = C1) C2 C0)).
pose fb z := (Yo (z = C0) C2 (Yo (z = C1) C0 C1)).
pose fc H z := (J (P z) (Yo (inc (P z) H) (fa (Q z)) (fb (Q z)))).
pose f H := Lf(fc H) F F.
suff injf: injection (Lf f (\Po E) (derangements F)).
  by  move:(inj_source_smaller injf); aw.
have t1: inc C0 C3 by apply /setU1_P; left; fprops.
have t2: inc C1 C3 by apply /setU1_P; left; fprops.
have t3: inc C2 C3 by apply /setU1_P; right; fprops.
move:C2_ne_C01 C1_ne_C0 C0_ne_C1  => [tpne4 tpne7] tpne5 tpne6.
have tpne3: C1 <> C2 by apply : nesym.
have tpne8: C0 <> C2 by apply:nesym.
have pb: forall v, sub v E -> lf_axiom (fc v) F F.
  move => v vE z /setX_P [za zb zc]; apply: setXp_i => //.
  rewrite /fa/fb; Ytac p1; Ytac p2; fprops; Ytac p3; fprops.
have pc: forall t, inc t E -> inc (J t C0) F by move => t tE;apply /setXp_i. 
apply: lf_injective.
  move => u /setP_P uE; move: (pb _ uE) => ax1; rewrite /f.
  have t3d: forall x, inc x C3 -> x <> C0 -> x <> C1 -> x = C2.
    by move => x /setU1_P [] // /set2_P; case.
  have bfu: bijection (f u).
    have fc3: forall y, inc y F -> fc u (fc u (fc u y)) = y.
     move => y /setX_P [p1 p2 p3]; rewrite - {2} p1.
     rewrite /fc !pr1_pair !pr2_pair; apply: f_equal;  Ytac pu; Ytac0; Ytac0;
     rewrite /fa/fb; case: (equal_or_not (Q y) C0) => p4; Ytac0;
       try (Ytac0; Ytac0; Ytac0; Ytac0 => //);
      case: (equal_or_not (Q y) C1) => p5; Ytac0;
       try (Ytac0; Ytac0; Ytac0; Ytac0 => //); symmetry; apply: t3d => //.
    apply: lf_bijective => //.
      by move => x y xF yF h; rewrite - (fc3 _ xF) - (fc3 _ yF) h.
      move => y yF; exists (fc u (fc u y)).
        by  apply: (ax1); apply: ax1.
        by symmetry;apply: fc3.
  apply: Zo_i.
    by apply: Zo_i => //;apply /functionsP; red;saw; fct_tac.
  move => x xF; rewrite /fc/fa/fb LfV// => eq1; move: (f_equal Q eq1); aw.
  Ytac p1; Ytac p2; rewrite ? p2; fprops;Ytac p3; rewrite ? p3; fprops.
move => u v /setP_P uE /setP_P vE sf.
move: (pb _ uE)(pb _ vE) => ax1 ax2.
set_extens t => tu.
  move: (pc _ (uE _ tu)) => pF.
  move: (f_equal (fun z => (Q (Vf z(J t C0)))) sf); rewrite /f/fc ! LfV//; aw.
  Ytac0; Ytac tv => //; rewrite /fa/fb; Ytac0; Ytac0; Ytac0; Ytac0 => //.
move: (pc _ (vE _ tu)) => pF.
move: (f_equal (fun z => (Q (Vf z (J t C0)))) sf); rewrite /f/fc !LfV//; aw.
by Ytac0; Ytac tv => //; rewrite /fa/fb; Ytac0; Ytac0; Ytac0; Ytac0.
Qed.  


(** Exercise 6.6 *)
Section Exercise6_6.
Variables E F: Set.
Hypothesis Einf: infinite_set E.
Hypothesis leFE: (cardinal F) <=c (cardinal E).
Hypothesis Finf:  exists a b, [/\ inc a F, inc b F & a <> b].

Lemma Exercise6_6a: 
  exists G, [/\ sub G E, G =c E &  (E -s G) =c F].
Proof.
move: Einf => /infinite_setP ise1. 
move:(csum_inf leFE ise1); aw.
have pc:= (disjointU2_pr3 E F C1_ne_C0).
rewrite csum2cl csum2cr -(card_card (CS_sum2 E F)) pc.
set E1:=  E *s1 C0; set F1:= F *s1 C1.
move=>  /card_eqP [f [bf sf tf]].
move: (bf) => [injf sjf].
have sc1: sub E1 (source f) by rewrite sf; apply: subsetU2l.
have sc2: sub F1 (source f) by rewrite sf; apply: subsetU2r.
have ff: function f by fct_tac.
have sc3: sub (Vfs f E1) (target f) by apply: fun_image_Starget1.
exists (Vfs f E1); split => //; first by rewrite -tf.
  by rewrite (cardinal_image sc1 injf) /E1; aw.
move: (inj_image_C injf (refl_equal (source f)) sc1).
have ->: (source f) -s E1 = F1.
   rewrite sf setCU2_l setC_v set0_U2; set_extens t;first by move => /setC_P [].
   move => ta; apply /setC_P;split => // /indexed_P [_ _ qa].
   move /indexed_P: ta => [_ _]; rewrite qa; fprops.
rewrite -/(Imf f) (surjective_pr0 sjf) tf => <-.
by rewrite (cardinal_image sc2 injf)/F1; aw.
Qed.

Lemma Exercise6_6b: 
  (functions E F) =c  (surjections E F).
Proof.
move: Exercise6_6a => [G [sGE /card_eqP[f [bf sf tf]] /card_eqP[g [bg sg tg]]]].
symmetry;apply: cleA; first by apply: sub_smaller; apply: Zo_S.
pose C h x := Yo (inc x G) (Vf h (Vf f x)) (Vf g x).
pose Cx h := Lf (C h) E F.
move: bf bg => [[ff _] sjf] [[fg _] sjg].
set s1 := (functions E F);set s3 :=  (surjections E F).
have pd: forall u, inc u s1 -> lf_axiom (C u) E F.
  move=> u /functionsP [fu su tu].
  move=> t te; rewrite /C; Ytac tG; [ rewrite -tu | rewrite -tg] ;Wtac.
    rewrite su -tf; Wtac.
  rewrite sg;  apply /setC_P;split => //.
have pe: forall u, inc u s1 -> surjection (Cx u).
  move=> u us1; move: (pd _ us1) => ta.
  apply: lf_surjective => // y yF; rewrite -tg in yF.
  move: ((proj2 sjg) _  yF) => [z zsg ->].
  move: zsg; rewrite sg => /setC_P [ze nzg]; ex_tac.
  by rewrite /C; Ytac0.
have pf: lf_axiom Cx s1 s3.
  move=> u us1; move: (pe _ us1) => sC.
  apply: Zo_i =>//; apply /functionsP; rewrite /Cx; red;saw; fct_tac.
have pa: s1 = source (Lf Cx s1 s3) by aw.
have pb: s3 = target (Lf Cx s1 s3) by aw.
rewrite pb {1} pa;apply: inj_source_smaller; apply: lf_injective => //.
move=> u v us1 vs1; move: (pd _ us1) (pd _ vs1) => ta1 ta2.
move: us1 vs1 => /functionsP [fu su tu] /functionsP [fv sv tv] sC.
apply: function_exten => //; try ue.
move=> x; rewrite su -tf => xtf.
move: ((proj2 sjf) _ xtf) => [y ysf ->].
rewrite sf in ysf; move: (sGE _ ysf) => yE.
move: (f_equal (Vf^~y) sC); rewrite /Cx !LfV//.
by rewrite /C; Ytac0 ; Ytac0.
Qed.

Lemma Exercise6_6c (p:= \Po E) :
  (functions E F)  \Eq p /\ (sub_functions E F) \Eq p.
Proof.
set s1:= (functions E F); set s2 := (sub_functions E F).
move:  (Exercise6_5a E F); rewrite -/s1 -/s2 => prop1.
move: Finf => [a [b [aF bF ab]]].
have pb: (cardinal p) <=c (cardinal s1).
  pose f A x := Yo (inc x A) a b.
  have ta: forall A,  lf_axiom (f A) E F.
    by move=> A t tE; rewrite /f; Ytac xE.
  pose fA A := Lf (f A) E F.
  have pb:forall u v : Set, inc u p -> inc v p -> fA u = fA v -> sub u v.
    move=> u v; rewrite /p /fA => /setP_P uE /setP_P vE sf t tu.
    move: (ta u) (ta v) => ta1 ta2; move: (uE _ tu) => tE.
    move: (f_equal (Vf^~t) sf); rewrite /f !LfV//; Ytac0; Ytac yv => //.
  have ij: injection (Lf fA p s1).
    apply: lf_injective.
      move=> A As3; rewrite /fA;apply /functionsP;red;saw.
      apply: lf_function; apply: ta.
    move=> u v us3 vs3 sf; apply: extensionality; apply: pb => //.
  by move: (inj_source_smaller ij); aw.
move: (Exercise6_5b E F). rewrite -/s2 -/p.
have ->: (cardinal (\Po (product E F)) = cardinal p).
 rewrite /p ! card_setP;apply: cpow_pr; fprops.
 by apply: cprod_inf3 => //; exists a.
move=> pa.
have pe:= (cleA pa (cleT pb prop1)). 
have pe':= (cleA (cleT prop1 pa) pb).
by split; apply /card_eqP.
Qed.

End Exercise6_6.



(** Exercise 6.7 *)

Lemma Exercise6_7a E F  (B := injections E F) 
    (C := Zo (\Po F)(fun x => x =c E)):
    (cardinal C) <=c (cardinal B).
Proof.
apply: surjective_cle.
exists (Lf  (fun f => (Imf f)) B C); saw.
have pa: lf_axiom (fun f => (Imf f)) B C.
  move=> f => /Zo_P [] /functionsP [ff sf tf] injf.
  apply:Zo_i; last by move: (cardinal_range injf); rewrite sf.
  by apply /setP_P; rewrite -tf; apply:Imf_Starget.
apply: lf_surjective => //.
move=> y => /Zo_P [] /setP_P yF/card_eqP /EqS [f [bf sf tf]].
have ta: lf_axiom (Vf f) E F.
  move=> t; rewrite - sf => zE; apply: yF; rewrite -tf.
  apply: Vf_target => //; fct_tac.
move: bf => [[ff injf] sjf]. 
have fi: injection (Lf (Vf f) E F).
  apply: lf_injective =>// u v uE vE; by apply: injf; rewrite sf.
have ffi:function (Lf (Vf f) E F) by fct_tac.
exists (Lf (Vf f) E F). 
  apply: Zo_i =>//; apply /functionsP;saw.
symmetry;set_extens t.
   move /(Imf_P ffi); aw; move => [x xE];rewrite LfV// => ->; Wtac.
rewrite - tf;move => ty; apply  /(Imf_P ffi); aw.
by move: ((proj2 sjf) _  ty); rewrite sf; move=> [x xE ->]; ex_tac; rewrite !LfV.
Qed.

Lemma image_by_fun_injective f u v:
  injection f -> sub u (source f) -> sub v (source f) ->
  Vfs f u = Vfs f v -> u = v.
Proof.
move=> [ff injf]; move: u v.
have aux: forall u v, sub u (source f) -> sub v (source f) ->
  Vfs f u = Vfs f v ->  sub u v.
  move=> u v usf vsf aux t tu.
  have : inc (Vf f t) (Vfs f u) by apply /(Vf_image_P ff usf); ex_tac.
  rewrite aux;move  /(Vf_image_P ff vsf)=> [w wv sf].
  by rewrite (injf _ _ (usf _ tu) (vsf _ wv) sf).
move=> u v usf vsf auw; apply: extensionality; apply: aux =>//.
Qed.

Lemma Exercise6_7b E F (A:= functions E F) (B := injections E F)
    (C:= Zo (\Po F)(fun x => x =c E)):
  infinite_set F ->  (cardinal E) <=c (cardinal F) ->
  (cardinal A = cardinal B /\  cardinal A = cardinal C).
Proof.
move => infF leEF.
case: (emptyset_dichot E) => ne.
  have -> : C= singleton emptyset.
    apply:set1_pr.
       by apply/ Zo_P;split;[apply /setP_P | rewrite ne]; fprops.
       move => z /Zo_P [_]; rewrite ne cardinal_set0; apply: card_nonempty.
  rewrite cardinal_set1.
  move: (@fun_set_small_source F); rewrite -ne -/A => sA.
  set f:= empty_function_tg F.
  have injf: injection f.
    move: (empty_function_tg_function F) => [xa xb xc].
    by split => // x y; rewrite xb => /in_set0.
  have fA: inc f A. 
    rewrite /A /f/empty_function_tg. 
    by apply /functionsP; red;aw;split => //; fct_tac.
  have As: A = singleton f.
    by set_extens t; [ move=> tA; apply /set1_P;apply: sA | move /set1_P=> -> ].
  have Bs: B = singleton f.
    set_extens t; aw; first by move => /Zo_P; rewrite -/A As; case.
    by move /set1_P => ->; apply: Zo_i.
  rewrite As Bs ! cardinal_set1; split => //.
have prop1:cardinal A = cardinal B.
  symmetry;apply: cleA.
    have pa: sub B A by apply: Zo_S.
    apply: (sub_smaller pa).
  move/card_eqP: (cprod_inf3 ne leEF infF) => [g [bg sg tg]].
  pose Cf f := Lf (fun x => Vf g (J (Vf f x) x)) E F.
  suff pa: injection (Lf Cf A B) by move: (inj_source_smaller pa); aw.
  have pa: forall u x, inc u A -> inc x E -> inc (J (Vf u x) x) (source g).
    move=> u x; rewrite /A sg;move=> /functionsP [fu su tu] xE.
    apply: setXp_i => //; rewrite -tu; Wtac.
  have pb: forall u, inc u A -> lf_axiom (fun x=> Vf g (J (Vf u x) x)) E F.
    move=> u uA x xE; rewrite -tg; apply:Vf_target;[fct_tac | by apply: pa].
  move: bg => [[fg ig] sjg].
  have pc:lf_axiom Cf A B.
    move=> t tA.
    have aux: injection (Cf t).
      apply: lf_injective; first by apply: pb.
      move=> u v uE vE h;exact(pr2_def (ig _ _ (pa _ _ tA uE)(pa _ _ tA vE) h)).
    apply: Zo_i => //; rewrite /Cf;apply /functionsP;saw; fct_tac.
  apply: lf_injective => //.
  move=> u v uA vA; move: (pb _ uA) (pb _ vA) => ta1 ta2.
  move: (uA) (vA); move=>  /functionsP [fu su tu]  /functionsP [fv sv tv] sf.
  apply: function_exten => //; try ue; rewrite su => x xs.
  move: (f_equal (Vf^~ x) sf); rewrite /Cf !LfV// => sw.
  exact: (pr1_def (ig _ _ (pa _ _ uA xs) (pa _ _ vA xs) sw)).
split => //.
move: (cprod_inf3 ne leEF infF) =>/card_eqP aux.
move: (EqT (Eq_setX2_S E F) aux) => [g [bg sg tg]].
pose k f := Vfs g (graph f).
have pa: forall f, inc f A -> sub (graph f) (source g).
  move=> f /functionsP [ff sf tf].
  by rewrite sg - sf -tf; move: ff => [[_ qa] _].
have ig: injection g by move: bg => [ok _].
have ta: lf_axiom k A C.
  move=> f fA; move: (pa _ fA)=> ha; apply: Zo_i.
    apply /setP_P;rewrite /k -tg; apply: fun_image_Starget1; fct_tac.
  rewrite/k (cardinal_image ha ig).
  by move: fA => /functionsP [/Eq_src_graph /card_eqP <- ->  _]. 
have i1: injection (Lf k A C).
  apply: lf_injective => //.
  move=> u v uA vA; move: (pa _ uA) (pa _ vA) => g1 g2; move: uA vA.
  move=> /functionsP [fu su tu] /functionsP [fv sv tv] => aux2.
  apply: function_exten1 => //; last by ue.
  apply: (image_by_fun_injective ig) => //.
apply: cleA; first by move: (inj_source_smaller i1); aw.
rewrite prop1. apply: Exercise6_7a.
Qed.

(** Exercise 6.8 *)


Lemma Exercice6_8b E:
  (cardinal (permutations E)) <=c
   (cardinal (Zo (\Po (coarse E)) (fun r => worder_on r E))).
Proof.
set s3 := permutations E; set s2 := Zo _ _.
pose C f r:= graph_on (fun x y => gle r (Vf f x) (Vf f y)) E.
have Cp1: forall f  r, inc f s3 -> inc r s2 -> inc (C f r) s2.
  move=> f r => /Zo_P [] /functionsP [ff sf tf] bf.
  move /Zo_P => [] /setP_P rc [[or wor] sr]; apply: Zo_i.
    apply /setP_P; apply: Zo_S.
  have pa: forall a : Set, inc a E -> gle r (Vf f a) (Vf f a).
    by rewrite - sf => a aE; order_tac; rewrite sr -tf;Wtac.
  have sfr: substrate (C f r) = E.
    rewrite /C graph_on_sr //;split => //.
  have pb: order (C f r).
    rewrite /C; apply: order_from_rel1 => //.
      move=> x y z; simpl => le1 le2; order_tac.
    rewrite - sf => x y xE yE le1 le2; move: bf => [[_ injf] _].
    apply: injf =>//; order_tac.
  rewrite /worder;split => //; split => //;move=> x xE nex. 
  set X := Vfs f x.
  rewrite sfr in xE.
  have XE: sub X (substrate r).
    rewrite sr -tf;apply: fun_image_Starget1 => //.
  have sxt: sub x (source f) by rewrite sf.
  have neX: nonempty X.
    move: nex => [a ax]; exists (Vf f a); apply /(Vf_image_P ff sxt);ex_tac.  
  move: (wor _ XE neX) => [y []];rewrite iorder_sr //; move => yX ylX.
  move: yX => /(Vf_image_P ff sxt) [u ux wu].
  have pc: sub x (substrate (C f r)) by ue.
  exists u; red; rewrite iorder_sr //;split => // a ax; apply /iorder_gle0P => //; apply /Zo_P;aw.
  split; first by apply: setXp_i;fprops.
  have wx: inc (Vf f a) X by apply /(Vf_image_P ff sxt); ex_tac.
  by move: (iorder_gle1 (ylX _ wx)); rewrite -wu.
have Cp2: forall f  r, inc f s3 -> inc r s2  -> order_isomorphism f (C f r) r.
  move=> f r fs3 rs2; move: (Cp1 _ _ fs3 rs2).
  move:fs3 rs2 => /Zo_P [] /functionsP [ff sf tf] bf.
  move => /Zo_P [] /setP_P rc [[or wor] sr] /Zo_P [] rc1 [[or1 wor1] sr1].
  split => //; first by split => //; ue.
  move => x y xsf ysr; split;first by move /Zo_P => [_]; aw.
  move => pa; apply /Zo_P;aw;split => //; apply: setXp_i => //; ue.
have cp3: forall f1 f2 r,  inc f1 s3 -> inc f2 s3  -> inc r s2 ->
   C f1 r = C f2 r -> f1 = f2.
  move=> f1 f2 r f1s3 f2s3 rs2 sv; move: (Cp2 _ _ f1s3 rs2)(Cp2 _ _ f2s3 rs2).
  rewrite - sv => p1 p2.
  move: (order_isomorphism_w p1) (order_isomorphism_w p2) => p3 p4.
  move: rs2 (Cp1 _ _ f1s3 rs2) => /Zo_P  [q1 [q2 q3]] /Zo_P [q4 [q5 q6]].
  have sr1: segmentp r (Imf f1).
    move: p1 => [_ _ [ [_ sj1] _ tf1] _ ].  
    rewrite (surjective_pr0  sj1) tf1; apply: substrate_segment; fprops.
  have sr2: segmentp r (Imf f2).
    move: p2 => [_ _ [ [_ sj1] _ tf1] _ ].  
    rewrite (surjective_pr0  sj1) tf1; apply: substrate_segment; fprops.
   exact (isomorphism_worder_unique q5 q2 sr1 sr2 p3 p4).
move: (Zermelo E) => [r [wor sr]].
have rs2: inc r s2. 
  apply: Zo_i => //; apply /setP_P;rewrite - sr. 
  apply: sub_graph_coarse_substrate; fprops.
have p3: injection (Lf (fun f => C f r) s3 s2).
  apply: lf_injective => //.
      by move=> f fe; simpl; apply: Cp1.
  by move=> u v us3 vs3 su; apply: (cp3 _ _ _ us3 vs3 rs2).
by move: (inj_source_smaller p3); aw.
Qed.

Lemma Exercice6_8c E: infinite_set E ->
  let s1 := Zo (\Po (coarse E)) (fun r => order_on r E) in 
    let s2 := Zo (\Po (coarse E))(fun r => worder_on r E) in 
  (s1 =c s2 /\ s2 =c (\Po E)).
Proof.
move=> isE s1 s2.
have: sub s2 s1  by move=> r /Zo_P [pa [[pb1 pb2] pc]]; apply /Zo_P.
move/ (sub_smaller) => le1.
have /sub_smaller: sub s1 (\Po (coarse E)) by apply: Zo_S.
rewrite (Exercise6_4a isE) => le3.
move: (Exercice6_8b E); rewrite (Exercice6_5h isE) -/s2 => le4.
split; [ exact:(cleA (cleT le3 le4) le1) | exact: (cleA (cleT le1 le3) le4)].
Qed.

(** Exercise 6.9 *)

Lemma Exercise6_9a n: natp n ->
   (Nint_co n = induced_order Nat_order (segment Nat_order n)).
Proof.
move =>nN; rewrite segment_Nat_order //.
move : Nat_order_wor => [[o2 _] sb].
move: (Nintco_wor n) => [o1 _].
rewrite -/(Nint n).
move: (@Nint_S1 n); rewrite - sb => si.
move: (iorder_osr o2 si)=> [o3 sr3].
rewrite -/(Nint n); apply: order_exten => //; first by fprops.
move=> x y; split. 
   move => h; move /(Nintco_gleP nN):(h) => [pa pb].
   move: h => /Zo_P [] /setXp_P [xi yi] _.
   move: (xi) (yi) => /Zo_P [xsr _] /Zo_P [ysr _].
   apply/iorder_gle0P => //;apply /Nat_order_leP; split =>//; rewrite /natp; ue.
move /iorder_gleP => [pa pb] /Nat_order_leP [pc pd pe].
by apply  /(Nintco_gleP nN);split => //; apply /(NintP nN).
Qed.


Lemma Exercise6_9 r: worder r ->
  (forall x, inc x (substrate r) ->
    (least r x \/ 
    has_greatest (induced_order r (segment r x)))) ->
  r \Is  Nat_order 
  \/ (exists2 n, natp n &  r \Is (Nint_co n)).
Proof.
move => wor hyp.
move: Nat_order_wor => [h1 s1].
case: (isomorphism_worder2 wor h1);first (by left); last first.
   move=> [n]; rewrite s1;move => nN io1; right => //; exists n => //.
   by rewrite (Exercise6_9a nN);apply: orderIS.
move=> [x xsr [f  [o1 o2 [bf sf tg] etc]]].
have pa: sub (segment r x) (substrate r) by apply: sub_segment.
move: wor => [or _];move: sf; aw => sf.
have sra :=  (proj2(seg_order_osr x or)).
rewrite s1 in tg.
case: (hyp _ xsr) => aux.
  have zt: inc \0c (target f) by rewrite tg ; apply: NS0.
  move: (inverse_Vis bf zt); rewrite sf sra => ys.
  move: (inc_segment ys) => ylt.
  move: aux => [a1 a2]; move: (a2 _  (sub_segment ys)) => yle; order_tac.
move: aux => [y]; rewrite /greatest iorder_sr //; move => [ysr yfg].
rewrite - sra -  sf in ysr.
have wb:(natp (Vf f y)) by rewrite/natp; Wtac; fct_tac.
set z := csucc (Vf f y).
have zb: inc z (target f)  by rewrite tg; apply/NS_succ.
have ys:= (inverse_Vis bf zb); move:(ys) ;rewrite  sf sra => ys1.
move:  (yfg _ ys1); rewrite (etc _ _ ys ysr).
rewrite  (inverse_V bf zb) /z.  
move /Nat_order_leP => [qa qb qc].
case: (cleNgt qc (cltS qb)).
Qed.

(** -- Exercise 6.10  points a b d  and part of c are in the main text 
we show here the remainder of c *)
Lemma aleph_pr9 x: ordinalp x ->
  let y:= (omega_fct x) in 
  let src := (osucc x) in
   let trg := Zo (cardinals_le y) infinite_c  in
  order_isomorphism
    (Lf (fun z => (omega_fct z)) src trg)
    (ole_on src)(ole_on trg).
Proof.
move=> ox y src trg.
have osrc: ordinalp src by apply: OS_succ.
move:(wordering_ole_pr (Os_ordinal osrc)) => [p2 p1].
move: p2 => [p2 _].
have cy: cardinalp y by apply: CS_aleph.
have cse:ordinal_set trg by move =>  t /Zo_P [_] [] []. 
have [[p3 _] p4]:=(wordering_ole_pr cse).
have ta:lf_axiom (fun z  => (omega_fct z)) src trg.
  move=> z;rewrite /src/trg; move /(oleP ox) => pa; apply /Zo_P; split.
    apply /cardinals_leP => //.  
      apply: (aleph_le_lec pa).
  have oz:= proj31 pa.
  apply: (CIS_aleph oz).
saw.
  saw => //; apply: lf_bijective => //.
    move => u v usr vsr.
    move: (Os_ordinal osrc usr)  (Os_ordinal osrc vsr) => oa ob.
    by apply: aleph_inj.
  move=> z /Zo_P  [] /(cardinals_leP cy) zy iz.
  move: (ord_index_pr1 iz)=> [ot tp].
  exists (ord_index z) => //. 
   rewrite /src; apply/oleP => //.
   by apply: aleph_lec_le => //; rewrite tp.
red;aw;move=> a b ais bis; rewrite !LfV//.
split; move /Zo_P => [] /setXp_P [pa pb]; aw => h; 
   apply: Zo_i; try apply:setXp_i => //; try apply: ta => //; aw. 
  by apply: aleph_le_leo.
move:(Os_ordinal osrc ais) (Os_ordinal osrc bis) => oa ob.
apply: aleph_leo_le => //. 
Qed.

(** -- Exercise 6.11; see main text *)

(** -- Exercise 6.12; (a) (v- is in the main text; 
(c) is here *)


Definition Ex6_12_e (n: Set) i:=  (Yo (i = n) \0o \1o).
Definition Ex6_12_c (f: fterm) n i := 
     (Yo (i = n) (Yo (n = \0c) \1o (f \1c)) 
            (Yo (csucc i = n) \1o (f (csucc (csucc i))))).
Definition  Ex6_12_ec (f: fterm) n i := J (Ex6_12_e n i) (Ex6_12_c f n i).
Definition  Ex6_12_ax f n:=
   (forall i, inc i (Nint1c n) -> posnatp (f i)).

Definition  Ex6_12_v f n:= CNFpv (Ex6_12_ec f n) n.

Lemma Exercise6_12a n: natp n -> n <> \0c ->
  (inc \1c (Nint1c n) /\ inc n (Nint1c n)).
Proof.
move => nN nz; split; apply/(Nint1cP nN); split; fprops.
apply /cge1P;apply: card_ne0_pos => //; fprops.
Qed.

Lemma Exercise6_12b f n: Ex6_12_ax f n -> natp n ->
  CNFp_ax (Ex6_12_ec f n) n.
Proof.
move: OS0 olt_01 PN1 => qa qb ac pb nN.
rewrite /Ex6_12_ec/Ex6_12_e /Ex6_12_c; split.
  move => i lin; rewrite (Y_false (proj2 lin))  (Y_false (proj2 lin)).
  split;aww; case: (equal_or_not (csucc i) n) => nsi; Ytac0=> //.
  have sin: csucc i <=c n by  apply/(cleSlt0P (proj31_1 lin) nN). 
  apply: pb; apply/(Nint1cP nN);split; first apply: succ_nz.
  by apply/(cleSlt0P (proj31 sin) nN). 
Ytac0; Ytac0; split;aww; Ytac b => //; apply: pb.
exact: (proj1 (Exercise6_12a nN b)).
Qed.

Lemma Exercise6_12c f g n:
  natp n -> Ex6_12_ax f n -> Ex6_12_ax g n ->
  Ex6_12_v f n =  Ex6_12_v g n -> 
  forall i, inc i (Nint1c n) -> f i = g i.
Proof.
move => nN pa pb eq.
move: (Exercise6_12b pa nN) (Exercise6_12b pb nN) => h1 h2.
move: (proj2 (CNFp_unique h1 h2 nN nN eq)) => h3.
move => i /(Nint1cP nN) [eq1 lein]. 
case: (equal_or_not n \0c) => nz. 
  by rewrite nz in lein; case:eq1; apply:cle0. 
move: (pr2_def (h3 n (cltS nN))); rewrite / Ex6_12_c; repeat Ytac0;move => sf1.
move: (cpred_pr (NS_le_nat lein nN) eq1) => [sa sb].
case: (equal_or_not (cpred i) \0c) => piz; first by rewrite sb piz succ_zero.
move: (cpred_pr sa piz) => [sa' sb']. 
have lt1: cpred i <c n by apply/(cleSltP sa); rewrite - sb.
move: (clt_ltT (cpred_lt sa piz) lt1) => [/(cltSleP nN) lt2 eq2].
move: (pr2_def (h3 _ lt2)); rewrite / Ex6_12_c - sb' - sb. 
by move: (proj2 lt1) => lt3; repeat Ytac0.
Qed.

Lemma Exercise6_12d n f: natp n -> Ex6_12_ax f n ->
  Ex6_12_v f n = Yo (n = \0c) \1o
    ((f \1c) *o oprodf
     (fun i => (osucc (omega0 *o (Yo (csucc i = n) \1o (f (csucc (csucc i)))))))
     n).
Proof.
move => nN pa.
rewrite /Ex6_12_v /CNFpv {1 2} /Ex6_12_ec /Ex6_12_e /Ex6_12_c.
aw; Ytac0; Ytac0.
case (equal_or_not n \0c) => nz; aw;repeat Ytac0. 
  by rewrite nz /CNFpv1 oprod_f0 oopow0 !(oprod1l OS1).
rewrite oopow0 (oprod1l  (OS_nat (proj1(pa _ (proj1 (Exercise6_12a nN nz)))))).
apply: f_equal.
apply:(oprodf_exten nN) => i [_ lin].
rewrite /Ex6_12_ec /Ex6_12_e /Ex6_12_c  /CNFp_value1/cantor_pmon.
by aw; rewrite /CNFp_value1 !(Y_false lin)  oopow1.
Qed.

Lemma Exercise6_12e p: 
  posnatp p -> p *o (osucc omega0) = (omega0 +o p).
Proof.
move/posnat_ordinalp => [np no]; move: (proj31_1 no) => on.
have h := (oprod_int_omega no np). 
by rewrite -(osucc_pr OS_omega)(oprodD OS_omega OS1  on) h (oprod1r on).
Qed.

Lemma Exercise6_12f f n: 
   natp n -> Ex6_12_ax f n -> 
   Ex6_12_v f n = oprodf (fun z => (omega0 +o f(csucc z))) n.
Proof.
move => nN ax; rewrite (Exercise6_12d nN ax) /CNFpv1.
Ytac nz; first by rewrite nz oprod_f0.
move: (cpred_pr nN nz); set m := cpred n; move => [mB sv].
move: ax; rewrite sv; clear sv; move: m mB; clear n nN nz.
have Ha:= OS_succ OS_omega.
apply: Nat_induction.
  move:(proj2(Exercise6_12a NS1 (card1_nz))); rewrite - {2} succ_zero => H ax.
  move: (ax _ H) => sa.
  have os:= (OS_sum2 OS_omega (OS_nat (proj1 sa))).
  by rewrite succ_zero oprod_f1 succ_zero (Y_true (erefl \1c)) 
   (oprod1r OS_omega) // oprod_f1 succ_zero // (Exercise6_12e sa).
move => n nN Hrec ax.
have snN := NS_succ nN; have ssnN := NS_succ snN.
have ax2: Ex6_12_ax f (csucc n).
   move => i/(Nint1cP snN) [inz lein]; apply: ax; apply/(Nint1cP ssnN). 
   split => //; exact: (cleT lein (cleS snN)).
have nsn:= (proj2(cltS snN)).
rewrite (oprod_fS _ snN) (oprod_fS _ snN) - (Hrec ax2) ! (oprod_fS _ nN).
repeat Ytac0.
set w1 := oprodf _ _.
set w2 := oprodf _ _.
have <- : w1 = w2.
  apply: (oprodf_exten nN) => i lein.
  move: (clt_leT lein (cleS nN)) => [_ nin].
  Ytac h1; first by move: (csucc_inj (proj31_1 lein) (CS_succ n) h1).
  Ytac h2 => //.
  by move:(csucc_inj (proj31_1 lein) (proj32_1 lein) h2) (proj2 lein).
move: (Exercise6_12a ssnN (@succ_nz (csucc n))) => [/ax [ua _] /ax sa].
rewrite (oprod1r OS_omega) - (Exercise6_12e sa).
move: (CNFp_pr1 olt_01 sa); rewrite /CNFp_value1/CNFp_value2 oopow1 => ->.
have ow1: ordinalp w1. 
   apply:(OS_oprodf nN) => i lin; apply: OS_succ. 
   apply:(OS_prod2 OS_omega); Ytac y; fprops.
   move :(cleSS(cleSS (proj1 lin))) => h1.
   have ii: inc (csucc (csucc i)) (Nint1c (csucc (csucc n))).
     apply/(Nint1cP ssnN); split => //; apply: succ_nz.
   exact (OS_nat (proj1 (ax _ ii))).
have of1:=OS_nat ua.
move: (OS_prod2 ow1 Ha) (OS_nat (proj1 sa)) => owa ofn.
rewrite (oprodA ow1 Ha ofn) (oprodA of1 (OS_prod2 owa ofn) Ha).
by rewrite  (oprodA (OS_prod2 of1 owa) ofn Ha) (oprodA of1 owa ofn).
Qed.

Lemma Exercise6_12g n:
  natp n -> 
  factorial n = 
  cardinal (fun_image (permutations  (Nint1c n))
           (fun s => oprodf (fun i => (omega0 +o Vf s (csucc i))) n)).
Proof.
move => nN.
move: (card_Nint1c nN); set F := (Nint1c n) => cf.
have fsf: finite_set F by red; rewrite cf; apply /NatP.
set f :=  (fun s : Set => _).
rewrite - cf - (card_permutations fsf).
apply /card_eqP.
set E := permutations F; exists (Lf f E (fun_image E f)); saw.
have H: forall s, inc s E -> Ex6_12_ax (Vf s) n.
  move  => s /Zo_P [] /functionsP [fs ss ts] _ i ii.
  have: inc (Vf s i) F by rewrite - ts; Wtac; rewrite ss.
  move /(Nint1cP nN) => [sa sb]; exact:(posnat_prop (NS_le_nat sb nN) sa).
apply: lf_bijective.
+ move => t te; apply /funI_P; ex_tac.
+ move => u v ue ve. 
  move: (H  _ ue)  (H _ ve) => ax1 ax2.
  rewrite /f - (Exercise6_12f nN ax1) - (Exercise6_12f nN ax2) => eq.
  move: (Exercise6_12c nN ax1 ax2 eq) => h.
  move: ue ve => /Zo_S /functionsP [fs ss ts] /Zo_S /functionsP [fs' ss' ts'] .
  apply: function_exten; [exact | exact | by rewrite ss' | by rewrite ts'|].
  by move => i; rewrite ss; apply: h.  
+ by move => t /funI_P.
Qed.


(** -- Exercise 6.13. points a, c, d, e are in the main text. *)


Lemma ord_induction_p20 u w0 g b
  (f:= ord_induction_defined w0 g):
  OIax2 u w0 g ->
 ordinalp b -> exists2 E, finite_set E &
 forall y, (inc y E) <-> (exists x, [/\ u <=o x, ordinalp y & f x y = b]).
Proof.
move=> axx ob; move: (axx) => [ax1 _ _ _].
have fv: f = ord_induction_defined w0 g by done.
pose p x y:= [/\ u <=o x, ordinalp y & f x y = b].
set E := Zo (osucc b) (fun y => exists x, p x y).
exists E; last first.
  move=> y; split; first by move /Zo_P => [].
  move=> h; apply/Zo_P;split; last (by exact). 
  move: h=> [x [ux oy fb]]; apply /(oleP ob); rewrite - fb.
  exact: (ord_induction_p9 fv ax1 ux oy).
pose the_x y := choose (fun x => p x y).
have the_xp: forall y, inc y E -> p (the_x y) y.
  by move=> y yE; apply choose_pr; move: yE => /Zo_P [_].
pose the_lx y := least_ordinal (fun x => p x y) (the_x y).
have the_lxp: forall y, inc y E ->
     [/\ ordinalp (the_lx y) , p (the_lx y) y &
      (forall z, ordinalp z -> p z y -> (the_lx y) <=o z )].
  move=> y yE; move: (the_xp _ yE) => pv.
  move: (pv) =>  [[_ pw _] _ _].
  exact:(least_ordinal4 (p:= p ^~y) pw pv). 
have thex_dec: forall y1 y2, inc y1 E -> inc y2 E ->
    y1 <o y2 -> (the_lx y2) <o (the_lx y1).
  move=> y1 y2 /the_lxp [ox1 px1 minx1] /the_lxp [ox2 px2 minx2] y12.
  case: (oleT_el ox1 ox2) => le1 //.
  move: px1 px2 => [pa pb pc] [pd pe pf].
  move: (ord_induction_p16 fv axx pa le1 (oleR pb)).
  move: (ord_induction_p8 fv ax1 pd y12); rewrite pc pf  => lea lta.
  case: (oleNgt lta lea).
have ose: ordinal_set E by move=>  x => /Zo_P [_ [y [_ p3 _]]]. 
move: (wordering_ole_pr ose). 
set r:= ole_on E; move => [pd pc].
rewrite -pc; apply: well_ordered_opposite => //.
move: pd => [pd pe].
move: (opp_osr pd) => [or1]; rewrite pc => sr1.
split; fprops; rewrite /has_least/least sr1 => X XE neX.
rewrite iorder_sr; [ | fprops | ue].
set Y := fun_image X the_lx.
have neY: nonempty Y .
   move: neX => [x xE]; exists (the_lx x); apply /funI_P; ex_tac.
have osy:  ordinal_set Y. 
  move=>  x /funI_P [y yx yv].
  by move: (the_lxp _ (XE _ yx)); rewrite yv; move=> [p1 _ _].
move: (wordering_ole_pr osy) => [pd1 pc1].
rewrite - pc1 in neY; move: (worder_least pd1 neY) => [y []].
rewrite pc1 => /funI_P [x xX xv] => xv1.
exists x; split => //;move => t tX; apply /iorder_gle0P => //.
apply /opp_gleP/graph_on_P1;split => //; try apply:XE => //.
have aux: inc (the_lx t) Y by apply /funI_P; ex_tac.
move: (xv1 _ aux) => /graph_on_P1 [p1 p2 p3].
have ox: ordinalp x by move: (ose _ (XE _ xX)).
have ot: ordinalp t by move: (ose _ (XE _ tX)).
case: (oleT_el ot ox) => le1 //.
by move: (thex_dec _ _  (XE _ xX) (XE _ tX) le1); rewrite - xv => /(oleNgt p3).
Qed.

(** Exercise 6.14 *)

Lemma rev_succ_pr x: ordinalp x ->
  x <o omega0 \/ x = \1o +o x.
Proof. by case /(oleT_el OS_omega); [ move/osum_1inf; right | left]. Qed.


Lemma ord_square_inj a: ordinalp a ->
   a ^o \2o =  (a *o \2o) ^o \2o -> a = \0o.
Proof.
move => oa.
case: (ozero_dichot oa) => az; first by exact.
have s1: osucc \1c = \2o by rewrite osucc_one.
have oa2:= (OS_prod2 oa OS2).
have e1: forall u, ordinalp u -> u *o u = u ^o \2o.
  by move=> u ou; rewrite - s1 (opow_succ ou OS1) (opowx1 ou). 
rewrite - (e1 _ oa) - (e1 _ oa2) => eq.
have e2: a = \2o *o (a *o \2o).
   move: eq; rewrite - (oprodA oa OS2 oa2) => h.
   exact: (oprod2_simpl oa (OS_prod2 OS2 oa2) az h).
have ha:=(oprod_Mle1 oa olt_02).
move:(oprod_M1le olt_02 oa2) ; rewrite - e2 => hb.
move:(oleA ha hb) =>eq2.
by case: card_12; exact: (esym (oprod2_simpl1 OS2 az (esym eq2))).
Qed.

Lemma critical_product_P2: 
  let CP := critical_ordinal \1o oprod2 in
  let p1 := fun y => [/\ infinite_o y, ordinalp y &
       (forall z, \1o <o z -> z <=o y ->
          exists2 t, ordinalp t &  y = z ^o t)] in
  forall y, CP y <-> p1 y.
Proof.
move=> CP p1 y.
have Hc: infinite_o y /\ ordinalp y <-> omega0 <=o y.
  split.
    move =>[qa qb];move/ (omega_P1 qb): qa=> sop; split => //; apply:OS_omega.
  by move => [_ qa qb]; split => //; move/(omega_P1 qa): qb.
move: (critical_productP y) => [Ha Hb].
split.
  move/Hb/Ha => [oy etc]; move/Hc: (oy) => [qa qb]; split => //. 
  by move=> z z1 z2; move: (etc _ z1 z2) => [t [t1 t2 t3]]; exists t.
move=> [ify oy hy]; move/Hc: (conj ify oy) => loy.
have lt1y:= (olt_leT olt_1omega loy).
split => //  x le1x ltxy; move:(ltxy) => [lexy nexy].
have ox:= proj31 lexy.
move:(olt_leT olt_01 le1x) => xp.
case: (oone_dichot xp) => xl1; first by rewrite xl1 (oprod1l oy).
move: (hy _ xl1 lexy) => [t ot yt].
case: (rev_succ_pr ot); last first. 
  by rewrite {1} yt - {1} (opowx1 ox)  - (opow_sum ox OS1 ot) => <-.
have yn1:= nesym (proj2 lt1y).
have xl2: \2o <=o x by apply oge2P.
move => tf; move: yt.
case: (ozero_dichot ot); first by move => ->; rewrite opowx0.
move=> tnz yt. apply: oleA; last by apply: oprod_M1le.
move: OS0 OS1 OS2 olt_02=> os0 os1 os2 l02.
case: (equal_or_not t \2o) => tnt.
  move: (opow_Mspec2 OS2 xl2).
  rewrite - {2} tnt -yt => leby.
  have xx: y = x *o x.
    rewrite yt tnt - osum_11_2 opow_sum // opowx1 //.
  have lexx2: x <=o  (x *o \2o) by apply: oprod_Mle1.
  have b1:= olt_leT xl1 lexx2.
  move: (hy _ b1 leby) => [u ou yuv].
  case: (ord2_trichotomy ou) => uz; first by move: yuv; rewrite uz opowx0.
    move: yuv; rewrite uz (opowx1 (proj32 lexx2)) => eq1.
    rewrite {1} eq1 oprodA // xx -{1} xx eq1 - oprodA //.
    apply: oprod_Mlele; fprops.
    case: (oleT_el OS_omega ox) => oxo.
      have l2o: \2o <o omega0 by  apply:olt_2omega.
      exact: (oleT(proj1 (oprod2_lt_omega l2o l2o)) oxo).
    by move: (oprod2_lt_omega oxo oxo); rewrite - xx => /(oleNgt loy).
  move: (odiff_pr uz) =>[]; set v := u -o \2o => v1 v2.
  move: yuv; rewrite v2 opow_sum //; last by fprops.
  set w := ((x *o \2o) ^o \2o) => le1.
  have od: ordinalp (x *o \2o) by fprops.
  have : y = w.
     apply: oleA.
       rewrite /w yt tnt; apply: (opow_Mleeq (nesym (proj2 xp)) lexx2 OS2).
      rewrite le1; apply: oprod_Mle1; rewrite /w; fprops.
    apply:(opow_pos) => //; apply: oprod2_pos => //.
  rewrite /w yt tnt; move => /(ord_square_inj ox) => h. 
  by move: (proj2 xp); rewrite h; case.
rewrite {1} yt - {1} (opowx1 ox)  - opow_sum //.
have tb: natp t by  apply /olt_omegaP.
have tnz':= nesym (proj2 tnz).
move: (cpred_pr tb tnz') => []; set u := (cpred t) => [uB tsu].
have uo: u <o omega0 by apply /olt_omegaP.
have ou:= proj31_1 uo.
have us: t = osucc u.
  by rewrite tsu; apply: succ_of_finite; move: uB => /NatP.
set z := x ^o u.
case: (equal_or_not u \0o) => unz.
   case: nexy; rewrite yt tsu unz // succ_zero opowx1 //.
have z1: \1o <o z. 
  by rewrite /z  - (opowx0 x) - opow_Meqltr //; apply:ord_ne0_pos.
have oz:= proj32_1 z1.
have z2: z <=o y. 
   rewrite /z yt; apply: opow_Meqle => //.
   by rewrite us;move: (oltS ou) => [ok _].
move: (hy _ z1 z2) => [v ov].
case: (ord2_trichotomy ov).
    by move => ->; rewrite opowx0.
  move => ->; rewrite opowx1 // /z us yt.
  move=> se; move: (opow_regular xl2 ot ou se); rewrite us => bad.
  by move: (oltS ou) => [_]; rewrite bad. 
move=> v2.
have le1: (u +o u <=o (u *o v)).
  rewrite - (ord_double ou); apply: oprod_Meqle => //.
suff aux : ((\1o +o osucc u) <=o (u +o u)).
  move => yv; rewrite yv /z - opow_prod //.
  apply: opow_Meqle => //; rewrite us; exact: (oleT aux le1).
have ->: \1o +o osucc u = u +o \2o.
  have oB := NS1.
  have tB:= NS2.
  have su: natp (osucc u) by ue.
  have fcu: finite_c u by apply /NatP.
  rewrite osum2_2int // osum2_2int // - succ_of_finite // (Nsucc_rw uB).
  by rewrite csumC - csumA csum_11.
apply: osum_Meqle => //.
case: (ord2_trichotomy ou);[ done |  move => u1 | done ].
by case: tnt; rewrite us u1 osucc_one.
Qed.


Lemma critical_product_pr3 a b:  \1o <o a -> \1o <o b ->
 indecomposable b -> 
 critical_ordinal \1o oprod2 (a ^o b).
Proof.
move=> a1 b1 bi.
have ob:= proj32_1 b1.
move: (indecomp_prop3 bi) => [c oc bv].
apply/(proj2 (critical_productP  (a ^o b))).
suff: exists m, [/\ ordinalp m,indecomposable m& a ^o b = omega0 ^o m].
  move=> [m [om im ->]].
  move: (indecomp_prop3 im) => [n nc -> ].
  by exists n.
case:(ozero_dichot oc) => cp.
  by move: b1; rewrite bv cp oopow0; move => [].
have blim: limit_ordinal b.
  by case: (indecomp_limit bi) => // e1; case: (proj2 b1). 
have aux t : \0o <o t ->  indecomposable (t *o b).
   by move => tp;move/(indecomp_prodP b1 tp): bi.
have x2: \2o <=o a by apply /oge2P.
have oa:= proj32 x2.
case: (oleT_el OS_omega oa) => fina.
  rewrite(CNF_pow_pr4 fina blim).
  have dp := (odegree_infinite fina); have od := (OS_prod2 (proj32_1 dp) ob).
  exists (odegree a *o b); split => //.
  by apply/(indecomp_prodP b1 dp).
move: (CNF_pow_pr5 x2 fina blim) => [z [oz sb sc]]; exists z; split => //.
case: (ozero_dichot oz)=> zp.
  by case: (proj2 (proj1 bi)); rewrite sb zp oprod0r.
case: (equal_or_not \1o z) => ez1; first by rewrite - ez1; exact: indecomp_one.
have z1: \1o <o z by split; [ apply/oge1P | ].
apply /(indecomp_prodP z1 olt_0omega); ue.
Qed.




(** ** Exercises of Section 6 *)

(** Exercise 6.15 *)

Section Exercise6_15.
Variable (b: Set).
Hypothesis bg2: \2o <=o b.

Definition CNFB_expos x := cnf_exponents (the_CNFB b x).

Lemma CNFB_monomial_inj  x (z :=  (the_CNFB b x)):
  ordinalp x ->
  {when inc ^~ (domain z) & , injective (oexp z)}.
Proof.
move => ox; move:(the_CNF_p0 bg2 ox) => [[fgz nN pz ax] _] i j idx jdx sv.
move:  (CNF_exponents_sM nN (proj1 ax)) => M.
case: (NleT_ell (NS_inc_nat nN idx) (NS_inc_nat nN jdx)).
- by move ->.
- move => lij; move/(NltP nN): jdx  => jdx.
  by case:(proj2(M _ _  lij jdx)).
- move => lij; move/(NltP nN): idx  => idx.
  by case:(proj2(M _ _  lij idx)).
Qed.

Lemma CNFB_range_fgraph x : ordinalp x -> fgraph (range (the_CNFB b x)).
Proof.
move => ox.
move:(the_CNF_p0 bg2 ox) => [[fgz nN pz ax] _].
split; first by move => t/(range_gP fgz) [i /pz pp ->].
move => i j /(range_gP fgz) [n nds ->] /(range_gP fgz) [m mds ->] sp.
by rewrite (CNFB_monomial_inj ox nds mds sp).
Qed.

Lemma CNFB_card_range x (z :=  (the_CNFB b x)):
  ordinalp x ->  domain z = cardinal (range z).
Proof.
move => ox; move:(the_CNF_p0 bg2 ox) => [[fgz nN pz ax] _].
set f := Lf (Vg z) (domain z) (range z).
rewrite - (card_nat nN).
suff: bijection f by move/equipotent_aux => /card_eqP.
apply: lf_bijective.
- by move => t/(inc_V_range fgz).
- move => u v udx vdx sv; apply: (CNFB_monomial_inj ox udx vdx).
  by rewrite/oexp sv.
- by move => t /(range_gP fgz). 
Qed.

Lemma CNFB_expos_zero: CNFB_expos \0o = emptyset.
Proof.
rewrite /CNFB_expos  (the_CNF_p1 bg2) /cnf_exponents.
by rewrite/domain/range funI_set0 funI_set0.
Qed.
  
Lemma CNFB_e_p2 x (E := CNFB_expos x):
  ordinalp x -> (finite_set E /\ ordinal_set E).
Proof.
move => ox.
move:(the_CNF_p0 bg2 ox) => [[fgz nN pz ax] _].
have aux: cardinal E = domain (the_CNFB b x).
  rewrite (CNFB_card_range ox).
  by apply: cardinal_fun_image; move: (proj2 (CNFB_range_fgraph ox)).
split.
  by apply/NatP; rewrite aux.
move => t  /funI_P [z /(range_gP fgz) [i idy ->]->].
by apply: (proj42 (proj1 ax));apply/(NltP nN).
Qed.


Lemma CNFB_e_p3 e c n:
  natp n -> CNFb_ax b e c (csucc n) ->
  e n <=o  (CNFbv b e c (csucc n)).
Proof.
move => nB ax; move: (CNFq_pg4 nB ax) => sa.
move:(ax) => [[_ sb _ _] _]; move: (sb _ (cltS nB)) => op.
move: (oleT (opow_Mspec2 op bg2) sa) => le2.
exact:(oleT (oprod_M1le (olt_leT olt_02 bg2) op) le2).
Qed.

Lemma CNFB_e_p4 x:
  ordinalp x -> (forall y, inc y (CNFB_expos x) -> y <=o x).
Proof.
move => ox y.
case: (ozero_dichot ox) => xz.
  by rewrite xz CNFB_expos_zero => /in_set0.
move:(the_CNF_p0 bg2 ox) => [[fgz nN zp ax] sv].
move:(the_CNF_p2 bg2 xz) => []; set m := cnf_size _ => mN mv.
move/funI_P =>[z /(range_gP fgz) [i idz -> ] ->].
rewrite mv in idz ax; move /(NleP mN): idz => lim.
move: (CNF_exponents_M (NS_succ mN) (proj1 ax) lim (cltS mN)) => le1.
by move: (oleT le1 (CNFB_e_p3 mN ax)); rewrite - mv -/(CNFBv b _) sv.
Qed.

Definition b_critical x := b ^o x = x.

Lemma CNFB_e_p5 e c n (x := CNFbv b e c (csucc n)):
  natp n -> CNFb_ax b e c (csucc n) ->
  (e n = x ->  b_critical x)
   /\ (b_critical x -> (n = \0c /\ (e n = x))).
Proof.
move=> nN ax.
move:(CNFq_p1 b e c nN); rewrite -/x.
have bp :=(olt_leT olt_02 bg2).
set en:= (e n);set A := cantor_mon _ _ _ _; set B := CNFbv _ _ _ _ =>  xv.
have oen: ordinalp (e n).
  by move: (ax) => [[_ a2 _ _] _]; apply: (a2 _ (cltS nN)).
have cnp :=  ((proj2 ax) _ (cltS nN)).
move: (opow_Mspec2 oen bg2) => le1.
have op:= proj32 le1.
move: (oprod_Mle1  op cnp); rewrite -/(cantor_mon b e c n) -/A => le2.
have oA:=(CNFq_p0 (proj1 ax) (cltS nN)).
have le3: en <=o b *o en by apply oprod_M1le.
have le4:= (oleT le3 le1).
have le5:= (oleT le4 le2).
have ax1:=(CNFb_p5 nN ax).
have oB:= (OS_CNFq nN (proj1 ax1)).
have le7:= (osum_Mle0 oA  oB).
have pg: en = x -> B = \0o.
  rewrite xv; move=> es; rewrite es in le5.
  exact (osum2_a_ab oA oB (oleA le5 le7)).
split.
  by move=> ex; apply: oleA; [rewrite -{1} ex xv (pg ex) (osum0r oA) | ue].
rewrite /b_critical => ci.
have le6: en <=o x. by rewrite xv; apply: (oleT le5); apply:osum_Mle0.
move: (CNFq_pg1 nN (proj1 ax)); rewrite -/x -/e - {1} ci => le8.
case: (equal_or_not en x) => nex; last first.
  have xx: osucc en <=o x by apply /oleSltP.  
  case: (oltNge le8 (opow_Meqle bp xx)).
split => //; ex_middle n0.
move:(cpred_pr nN n0) => [mN mv].
move:(pg nex) ax1; rewrite /B mv => uu ax1.
by move: (proj2 (CNFq_pg5 mN ax1)); rewrite uu. 
Qed.

Lemma CNFB_e_p6 x (y:=CNFB_expos x): ordinalp x ->
   ((b_critical x  -> y = singleton x) /\
   (~ (b_critical x) -> forall a, inc a y -> a <o x)).
Proof.  
move => ox.
move:(the_CNF_p0 bg2 ox) => [[fgz nN pz ax] xv].
case: (ozero_dichot ox) => nz.
  split; first by rewrite nz /b_critical opowx0 => h;  case: card1_nz.
  by rewrite /y nz CNFB_expos_zero => _ t /in_set0.
move:(the_CNF_p2 bg2 nz) => []; set m := cnf_size _ => mN mv.
rewrite mv in ax.
move: (CNFB_e_p5 mN ax); rewrite -mv -/(CNFBv _ _) xv; move=> [ph pi].
have ha: inc m (domain (the_CNFB b x)) by rewrite mv; apply: Nsucc_i.
split.
   move=> cx; move: (pi cx) => [pj pk].
   pose z := (the_CNFB b x).
   have eq1: range z = singleton (Vg z m).
     apply: (set1_pr (inc_V_range fgz ha)) =>  u /(range_gP fgz) [i idx ->].
     by move: idx; rewrite mv pj succ_zero => /set1_P ->.
   by rewrite /y /CNFB_expos/ cnf_exponents eq1 /domain funI_set1 - pk.
move=> ncx.
move: (CNFB_e_p3 mN ax); rewrite - mv -/(CNFBv _ _) xv => le1.
have lt1: oexp (the_CNFB b x) m <o x by split => //; dneg h; apply: ph.
move => a /funI_P [d /(range_gP fgz)  [i idz ->] ->].
rewrite mv in idz ax; move /(NleP mN): idz => lim.
exact:(ole_ltT (CNF_exponents_M (NS_succ mN) (proj1 ax) lim (cltS mN)) lt1).
Qed.


Definition CNFB_expos_rec x:=
 induction_defined (fun z => union (fun_image z CNFB_expos)) 
    (CNFB_expos x).

Definition CNFB_expos_rec_nc x n :=
  Zo (Vf (CNFB_expos_rec x) n) (fun z => ~ (b_critical z)).

Lemma CNFB_e_p7 x n (y := Vf (CNFB_expos_rec x) n):
   ordinalp x -> natp n -> (finite_set y /\ ordinal_set y).
Proof.
move=> ox; rewrite /y; clear y; move : n.
move: (induction_defined_pr  (fun z => union (fun_image z CNFB_expos)) 
    (CNFB_expos x)).
rewrite -/(CNFB_expos_rec x); move=> [sg sjg gz gnz].
apply: Nat_induction.
  rewrite gz.
  exact (CNFB_e_p2 ox).
move => n nB [pa pb]; rewrite (gnz _ nB); split.
  rewrite - setUb_identity; apply: finite_union_finite.
   hnf;rewrite /identity_g; aw =>i idf; rewrite LgV//.
    move: idf => /funI_P [z zn ->].
    by move:  (CNFB_e_p2 (pb _ zn)) => [ok _].
 by rewrite /identity_g; aw; apply: finite_fun_image.
move=> t /setU_P [y ty] /funI_P [z zw yv].
move:  (CNFB_e_p2 (pb _ zw)) => [_ ok].
by rewrite - yv in ok; apply: ok.
Qed.

Lemma CNFB_e_p8 x n (f :=  (CNFB_expos_rec x)):
  ordinalp x -> natp n -> 
  CNFB_expos_rec_nc x n = emptyset ->
  ( (forall a, inc a (Vf f n) -> b_critical a)
  /\ (forall k, natp k -> n <=c k -> Vf f k = Vf f n)).
Proof.
move=> ox nB me.
pose q m := CNFB_expos_rec_nc x m = emptyset.
have pa: forall m, q m ->  (forall a, inc a (Vf f m) -> b_critical a).
  by rewrite /q => m h a aw; ex_middle anc; empty_tac1 a; apply: Zo_i.
move: (induction_defined_pr  (fun z => union (fun_image z CNFB_expos)) 
  (CNFB_expos x)); rewrite -/ (CNFB_expos_rec x) -/f.
move=> [sg sjg gz gnz].  
have pb: forall m, natp m -> q m -> (Vf f m = Vf f (csucc m) /\ q (csucc m)).
  move=> m mB qm.
  suff h:  Vf f m = Vf f (csucc m).
   by split => //; move: qm; rewrite /q /CNFB_expos_rec_nc h //.
  rewrite (gnz _ mB); move: (pa _ qm) => ax.
  move: (CNFB_e_p7 ox mB) => [_ osf].
  set_extens t.
    move => ts; apply /setU_P.
    move: (ax _ ts)  (CNFB_e_p6 (osf _ ts)) => cy [ h _].
    move: (h cy) => px; exists (singleton t); first by fprops.
    apply /funI_P; ex_tac.
  move /setU_P => [y ty] /funI_P [z zw yv].
  move: (ax _ zw)  (CNFB_e_p6 (osf _ zw)) => cy [ h _].
  by move: ty; rewrite yv (h cy) => /set1_P  ->.
split; first by apply: pa.
suff: forall k : Set, natp k -> n <=c k -> (q k /\ Vf f k = Vf f n).
  by move=> aux k kB nk; move: (aux _ kB nk) => [ _ ].
apply: Nat_induction.
  move=> aux; move: me; rewrite (cle0 aux); split => //.
move => k kB hrec nsk0.
case: (equal_or_not n (csucc k)) => nsk; first by  rewrite -nsk //.
move: (conj nsk0 nsk); move /(cltSleP kB) => h1.
move: (hrec h1) => [pc pd]; move: (pb _ kB pc) => [pe pf]; split => //; ue.
Qed.

Lemma CNFB_e_p9 x: ordinalp x ->
  exists2 n, natp n & CNFB_expos_rec_nc x n = emptyset.
Proof.
move=> ox; ex_middle aux.
have pa: forall n, natp n -> nonempty (CNFB_expos_rec_nc x n).
  move=> n nB; case: (emptyset_dichot (CNFB_expos_rec_nc x n)) => //.
  by move => p; case: aux; exists n.
pose T :=  (CNFB_expos_rec_nc x).
pose h n := \osup (T n).
have hp: forall n, natp n ->
   [/\ (forall a,  inc a (T n) -> a <=o h n),
     inc (h n) (T n) &
     forall a, inc a (T (csucc n)) -> a <o (h n)].
   move=> n  nB; move: (CNFB_e_p7 ox nB) => [fs os].
   have sT: sub (T n) (Vf(CNFB_expos_rec x) n) by apply: Zo_S.
   have osT: ordinal_set (T n) by move=> t aT; apply (os _ (sT _ aT)).
   have pX: (forall a : Set, inc a (T n) -> a <=o h n).
      by move=> a aT;  apply: ord_sup_ub.
   have pY: inc (h n) (T n).
     move:(wordering_ole_pr osT).
     set r := (ole_on (T n)); move=> [wor sr].
     move: (worder_total wor) => tor.
     have srt: sub (T n) (substrate r) by rewrite sr; fprops.
     move:  (sub_finite_set sT fs) => fsT.
     move: (finite_subset_torder_greatest tor fsT (pa _ nB) srt) => [g gr].
     move: tor => [or _].
     move: gr => []; rewrite iorder_sr // => p1 p2.
     have <- //: g = h n.
     apply: (oleA); first by apply: ord_sup_ub.
     apply: ord_ub_sup => //; first by apply: osT.
     move=> i iT; move: (iorder_gle1 (p2 _ iT)). 
     by move /graph_on_P1 => [_ _].
  split => //.
  move => a  /Zo_P [qa qb].
  move: (induction_defined_pr  (fun z => union (fun_image z CNFB_expos)) 
    (CNFB_expos x)); rewrite -/ (CNFB_expos_rec x).
  move=> [_ _ _ gnz].
  move: qa; rewrite (gnz _ nB) => /setU_P [y ay] /funI_P [z zT yv].
  rewrite yv in ay.
  move: (CNFB_e_p6 (os _ zT)) => [zp zq].
  case: (p_or_not_p (b_critical z)) => zc.
    by case: qb; move: ay; rewrite (zp zc) => /set1_P ->.
  move: ((zq zc) _ ay) => z1.
  by apply: (olt_leT z1); apply:pX;  apply: Zo_i.
have xx: forall n, natp n -> h (csucc n) <o h n.
  move=> n nB; move: (hp _ nB) => [_ _ p3]; apply: p3.
  by move:(hp _ (NS_succ nB)) => [_ p2 _].
set R:= fun_image Nat h.
have neR: nonempty R 
   by exists(h \0c); apply /funI_P; exists \0c => //; apply:NS0.
have osR: ordinal_set R.
  by move =>t /funI_P [n nB ->]; move: (xx _ nB) => [[_]].
move: (ordinal_setI neR osR); set t := intersection R.
move=> /funI_P [n nB nv]; move: (xx _ nB).
have hsi: inc (h (csucc n)) R. 
  by apply /funI_P;exists (csucc n) => //; apply:NS_succ.
move: (setI_s1 hsi); rewrite -/t nv.
move => th /oltP0  [oh _ ih].
by move: (ordinal_irreflexive oh (th _ ih)).
Qed.

End Exercise6_15.

(** Exercise 6.16 *)

Lemma Exercise6_16a r: total_order r -> exists2 X, 
  cofinal r X & (worder (induced_order r X)).
Proof.
move => [or tor];move: (Exercise2_2b or) => [X [Xsr worX ub]].
exists X => //; split => // x xsr. 
case: (inc_or_not x X) => xX; first by ex_tac; order_tac.
ex_middle h; case: xX; apply: ub.
split => // z zX; case: (tor _ _ xsr (Xsr _ zX)) => //.
move=> xz; case: h; ex_tac.
Qed.

Lemma cofinality'_pr1 r: total_order r ->
   (nonempty (cofinality' r) /\ ordinal_set (cofinality' r)).
Proof.
move => tor; rewrite /cofinality'.
move: (Exercise6_16a tor) => [X ta tb].
split.
   exists (ordinal (induced_order r X)); apply /funI_P; exists X => //.
   by apply: Zo_i => //; move: ta => [tc _]; apply /setP_P.
move=> x => /funI_P [z szf ->]; apply: OS_ordinal.
by move: szf => /Zo_hi [_].
Qed.

Lemma intersection_sub1 A B C:
   A = union2 B C -> (forall x, inc x C -> exists y, inc y B /\ sub y x)
   -> intersection A = intersection B.
Proof.
move=> -> h.
case: (emptyset_dichot B) => bne. 
  rewrite bne set0_U2.
  have -> //: C = emptyset. 
  by apply /set0_P => t /h [y []]; rewrite bne => /in_set0.
have neA: nonempty (B \cup C).
  by move: bne => [x xB]; exists x; apply /setU2_P; left.
set_extens t. 
   move /(setI_P neA) => aux; apply /(setI_P bne) => i iB; apply: aux; fprops.
move /(setI_P bne) => aux; apply /(setI_P neA) => i iB. 
case/setU2_P: iB => iB; first by apply: aux.
by move: (h _ iB) =>  [y [yB]]; apply; apply: aux.
Qed.

Lemma cofinal_trans r x y:
   order r -> cofinal r x -> cofinal (induced_order r x) y ->
   cofinal r y.
Proof.
move=> or [xsr cx]; move /(cofinal_inducedP or  xsr).
move=> [yx xy]; split; first by apply: sub_trans xsr.
move=> t tx; move: (cx _ tx) => [z zx zy].
move: (xy _ zx) => [u uy zu]; ex_tac; order_tac.
Qed.

Lemma cofinal_image r r' f x:  
    order_isomorphism f r r' -> cofinal r x -> 
    cofinal r' (Vfs f x).
Proof.
move=> [o1 o2 [bf sf tf] isf] [xsr cx].
have ff: function f by fct_tac.
have xsf: sub x (source f) by ue.
split.
  move=> t /(Vf_image_P ff xsf) [u ux ->]; rewrite - tf; Wtac.
rewrite - tf; move => y yt; move: (bij_surj bf yt) => [z zf ->].
rewrite sf in zf;  move: (cx _ zf) => [t tx ty].
exists (Vf f t); first by  apply/(Vf_image_P ff xsf); ex_tac.
rewrite -isf //; [ ue |  by apply: xsf].
Qed.

Lemma worder_image r r' f A: 
  order_isomorphism f r r' -> sub A (substrate r) ->
  let oa := (induced_order r A) in
  let ob := (induced_order r' (Vfs f A)) in
  worder oa  -> (worder ob /\ ordinal oa = ordinal ob).
Proof.
move=> isf Asr oa ob wo1.
move: (isf) =>  [o1 o2 [bf sf tf] isfo].
have ff: function f by fct_tac.
have sAs: sub A (source f) by ue.
have pa: sub (Vfs f A) (substrate r').
  move => t  /(Vf_image_P ff sAs) [u uA ->]; rewrite - tf; Wtac. 
move: (iorder_osr o2 pa) => [oob sob].
move: (bf) => [injf _].
move: (restriction1_fb injf sAs) => br.
have sr1: (source (restriction1 f A)) = A by rewrite /restriction1 ; aw.
have aux: forall x, inc x A -> inc (Vf f x) (Vfs f A).
  move => x xA; apply /(Vf_image_P ff sAs); ex_tac.
have abis: oa \Is ob.
   exists (restriction1 f A); split;fprops; first split => //.
       rewrite /oa sr1 iorder_sr//.
     by rewrite /ob /restriction1 iorder_sr //; aw.
   hnf;rewrite sr1; move=> x y xA yA. 
   move: (sAs _ xA) (sAs _ yA) => xs ys.
   rewrite restriction1_V // restriction1_V //. 
   by split;move / iorder_gleP => [qa qb qc]; apply /iorder_gleP;split => //;
       try (apply: aux =>//); apply/(isfo _ _ xs ys).
suff soob: worder ob by split => //; apply: ordinal_o_isu1.
split => //.
move: wo1 => [ _ ].
rewrite iorder_sr // iorder_sr // => wo1.
move => x xi nex; rewrite iorder_trans //.
set z:= Vfs (inverse_fun f) x.
move: (inverse_bij_fb bf) => ibf.
have fif: function (inverse_fun f) by fct_tac.
have sxt: sub x (target f) by apply: (sub_trans xi); apply: fun_image_Starget1.
have sxt1: sub x (source (inverse_fun f)) by aw.
have sxs: sub x (substrate r') by ue.
have nez: nonempty z. 
   move: nex => [w wx]; exists (Vf (inverse_fun f) w).
   apply /(Vf_image_P fif sxt1); ex_tac.
have za: sub z A.
  move=> t  /(Vf_image_P fif sxt1) [u ux ->].
  move: (xi _ ux) => /(Vf_image_P ff sAs); move=> [v vA ->].
  by rewrite  (inverse_V2 bf (sAs _ vA)).
move: (wo1 _ za nez); rewrite iorder_trans //; move => [y []].
have zr: sub z (substrate r) by rewrite - sf; apply: sub_trans sAs.
rewrite /has_least /least iorder_sr // iorder_sr //.
move /(Vf_image_P fif sxt1) => [z1 z2 ->] yl;exists z1; split => //.
move => a ax; apply /iorder_gleP => //.
set b := Vf (inverse_fun f) a.
have bz: inc b z by apply /(Vf_image_P fif sxt1); ex_tac. 
have atf: inc a (target f) by apply sxt.
have z1tf: inc z1 (target f) by apply sxt.
have qa: inc (Vf (inverse_fun f) z1) (source f) by apply: inverse_Vis.
have qb: inc (Vf (inverse_fun f) a) (source f) by apply: inverse_Vis.
move: (yl _ bz) => le1; move: (iorder_gle1 le1).
rewrite /b isfo //  (inverse_V bf z1tf) //  (inverse_V bf atf) //.
Qed.


(* regular_cofinal_si_unique : monter la premiere partie formellement, 
et deplacer les 2 theoremes en exercice
*)

(* --- *)

(** Exercise  6.10 *)
(* mettre aleph_pr9 *)


(*  exercise 6 19 *)


Lemma cofinality_pr6 a f (b:= omega_fct a): 
   ordinalp a -> 
   inc f (functions b b) ->
   exists g, inc g (injections b b) /\
   (forall x, inc x b ->  Vf f x <=o Vf g x).
Proof. 
move => oa /functionsP [ff sf tf].
move: (aleph_limit oa); rewrite -/b => lb.
move: (lb) => [ob zb plb].
move: (ordinal_o_wor ob); set r := ordinal_o _ => wor.
have sr: substrate r = b by rewrite /r ordinal_o_sr.
pose unsrc f:= Yo (inc (domain f) b) (domain f) \0o.
have cp3: forall x, inc (unsrc x) b by move=> x; rewrite /unsrc; Ytac h => //.
pose coer1 v y := intersection (b -s (v \cup y)).
pose coex v :=  (Yo (inc v b) v \0o).
pose p g := let s := unsrc g in  coex (coer1 (Vf f s) (direct_image g s)).
move: (transfinite_pr1 p wor); rewrite /transfiniteg_def sr.
set g:= transfiniteg_defined r p; move=> [fgg sg tgp].
pose Tf := direct_image g.
have cp0 u v: inc (coer1 u v) b.
  rewrite/coer1;set c := _ -s _;case: (emptyset_dichot c) => ce.
    by rewrite ce setI_0.
  have os: ordinal_set c by move => t /setC_P [/(Os_ordinal ob) tb _].
  by move: (ordinal_setI ce os) => /setC_P [].
have cp4 x: inc x b -> Vg g x = (coer1 (Vf f x) (Tf x)).
  move=> xb. 
  rewrite (tgp _ xb) /p /unsrc restr_d (ordinal_segment ob xb); Ytac0.
  rewrite/coex (Y_true (cp0 _ _)) (dirim_restr2 fgg) //.
  by rewrite sg; move/(oltP ob): xb => /proj1/proj33.
have ta: lf_axiom (Vg g) b b by move => t tb; rewrite (cp4 _ tb); apply:cp0.
have taa: forall x, inc x b -> lf_axiom (Vg g) x b.
   move=> x xb t ita; move: (ordinal_transitive ob xb ita); apply ta.
set h:= Lf (fun z => Vg g z) b b.
have hp x: inc x b -> Vf h x = Vg g x by  move =>  xsf; rewrite /h LfV.
have off1 x: inc x b -> inc (Vf f x) b by  move =>  xb; Wtac. 
have off2: forall x, inc x b -> ordinalp (Vf f x).
  by move => x  /off1 /(Os_ordinal ob).
have cp5: forall x, inc x b -> nonempty (b -s ((Vf f x) \cup (Tf x))).
  move => x xb.
  apply:(infinite_union2 (CIS_aleph oa)).
    have: Vf f x <o b  by move /(oltP ob): (off1 _ xb).
    by move/ (ocle2P (CS_aleph oa)  (off2 _ xb)).
  move /(oltP ob): xb => lxb. 
  move/(ocle2P (CS_aleph oa) (proj31_1 lxb)): (lxb) => lec2.
  have xsg: sub x (domain g) by rewrite sg; exact: (proj33 (proj1 lxb)).
  move:(range_smaller (restr_fgraph g x)).
  rewrite (dirim_restr fgg xsg) restr_d => cc; apply:(cle_ltT cc lec2).
have cp6 x: inc x b ->  inc (Vg g x) (b -s ((Vf f x) \cup (Tf x))).
  move => xb; move: (cp5 _ xb)=> ne.
  rewrite  (cp4 _ xb) /coer1; apply:(ordinal_setI ne).
  by move => t /setC_P [/(Os_ordinal ob) tb _].
have ra: function_prop h b b. 
  by rewrite /h; red; saw; apply: lf_function.
have rb: (forall x, inc x b -> Vf f x <=o Vf h x).
  move => x xb; rewrite (hp _ xb).
  move: (cp6 _ xb) => /setC_P [p1] /setU2_P p2.
  case: (oleT_el (off2 _ xb) (Os_ordinal ob p1)) => // /oltP0/ proj33 ok.
  by case: p2; left. 
exists h; split => //; apply:Zo_i;first by apply/functionsP.
apply: lf_injective => // u v ub vb sv.
have Ha x: inc x b -> ~ inc (Vg g x) (Tf x).
  by move => /cp6 /setC_P [p1] /setU2_P ww res; case: ww; right.
have Hb x y: inc x y -> inc y b -> inc (Vg g x) (Tf y).
  move => ixy yb; apply/dirim_P; ex_tac; apply:(fdomain_pr1 fgg).
  by rewrite sg; move: (ordinal_transitive ob yb ixy).
case: (ordinal_inA (Os_ordinal ob ub)(Os_ordinal ob vb))  => // cuv.
  by case:(Ha _ vb);  move: (Hb _ _ cuv vb); rewrite sv.
  by case:(Ha _ ub);  move: (Hb _ _ cuv ub); rewrite sv.
Qed.

Lemma cofinality_pr7 X b f (E :=  omega_fct b):
  ofg_Mle_leo X -> domain X = omega_fct b -> ordinalp b -> 
  limit_ordinal  (\osup (range X)) ->
  inc f (functions E (omega_fct (union (range X)))) ->
  exists2 g, inc g (injections E E) &
    (forall x, inc x (source f) ->  Vf f x <=o omega_fct (Vg X (Vf g x))).
Proof.
move=> [p1 p2 p2'] p4 p3.
have lb: limit_ordinal (domain X) by rewrite p4; apply: aleph_limit.
set a := (union (range X)) => la.
set E1 := functions E (omega_fct a).
set F2 := functions E E.
move => /functionsP [ff sf tf].
move: (p1)(lb) => fgX [p5 p5' p6].
move: (ofg_Mle_leo_os p1 p2) => p8.
have p9: forall t, inc t (omega_fct a) ->
    exists u, inc u E /\ t <=o  omega_fct (Vg X u).
    move => t ta.
    move: (la) => [oa _].
    move: (OS_aleph oa)  => pa0.
    move: aleph_normal => [_ ap1]; move: (ap1 _ la) => ap2.
    have ap3: (ordinal_set (fun_image a omega_fct)).
      move => u /funI_P [v ve ->]; apply (OS_aleph (Os_ordinal oa ve)).
    have ap4: t <o \osup (fun_image a omega_fct).
      by rewrite - ap2; apply /oltP.
    move: (olt_sup ap3 ap4) => [z ] /funI_P [w wa ->].
    move => le1.
    have le2: w  <o union (range X) by apply /oltP. 
    move: (olt_sup p8 le2) => [u q1 q2].
    move:q1 => /(range_gP fgX) [v vd vv].
    rewrite /E - p4; exists v; split => //; apply: (oleT (proj1 le1)).
    rewrite - vv; apply: (aleph_le_leo (proj1 q2)).
pose bv t := choose (fun u =>  inc u E /\ t <=o omega_fct (Vg X u)).
have p10: forall t, inc t (omega_fct a) -> 
      (inc (bv t) (omega_fct b) /\ t <=o omega_fct (Vg X (bv t))).
   move => t to;apply: (choose_pr (p9 _ to)).
pose bff := Lf (fun z => bv (Vf f z)) E E.
have p11:  lf_axiom (fun z : Set => bv (Vf f z)) E E.
  move => z ze.
  have wt: inc (Vf f z)(omega_fct a) by rewrite -tf; Wtac.
  by move: (p10 _ wt) => [].
have p12: inc bff F2.
   apply /functionsP;rewrite /bff;red;saw.
   apply: lf_function; apply: p11.
have p13: forall x, inc x (source f) -> Vf f x <=o omega_fct (Vg X (Vf bff x)).
  move => x xsf.
  rewrite sf in xsf; rewrite /bff LfV//.
  have wt: inc (Vf f x)(omega_fct a) by rewrite -tf; Wtac.
  by move: (p10 _ wt) => [].
move: (cofinality_pr6 p3 p12)=> [g [ge H]]; exists g=> //.
move => x xsf; move: (p13 _  xsf) => le1.
apply (oleT le1); apply: aleph_le_leo.
rewrite sf in xsf.
move: (H _ xsf) => h1. 
have q4: inc (Vf bff x) (domain X).
  by move: p12 => /functionsP [s1 s2 s3]; rewrite p4 -/E - s3; Wtac. 
have q5: inc (Vf g x) (domain X).
  move: ge => /Zo_P [] /functionsP [s1 s2 s3] _.
  by rewrite p4 /E - s3; Wtac;  rewrite s2. 
exact: (p2' _ _ q4 q5 h1). 
Qed.

Lemma infinite_increasing_power3 X b: 
  ofg_Mle_leo X -> domain X = omega_fct b -> ordinalp b -> 
  limit_ordinal  (\osup (range X)) ->
  cprod (Lg (domain X) (fun z => \aleph (Vg X z))) =
  \aleph (\osup (range X)) ^c \aleph b.
Proof.
move => si dx ob lb.
move: (si) => [fgf oob incx].
apply: cleA.
  have ->:  omega_fct b = cardinal (domain X).
    by rewrite dx card_card //; apply: CS_aleph.
  by apply: infinite_increasing_power_bound1.
set a :=  (\osup (range X)).
set E :=  (functions (omega_fct b) (omega_fct  (union (range X)))).
set F :=  (functions (omega_fct b) (omega_fct b)).
set F1 :=  (injections (omega_fct b) (omega_fct b)).
pose G g  := Lg (omega_fct b) (fun z => osucc (omega_fct (Vg X(Vf g z)))).
have pa: forall f, inc f  E -> exists2 g, 
   inc g F1 & inc (graph f) (productb (G g)).
   move => f fe; move: (cofinality_pr7 si  dx ob lb fe) => [g ge h].
   move: fe => /functionsP [ff sf tf].
   have pa: fgraph (G g) by rewrite /G; fprops.
   exists g => //; apply /setXb_P => //.
   rewrite /G; aw;split => //; [  fprops | by rewrite domain_fg | ].
   move => i isf; rewrite LgV//.
   rewrite - sf in isf; move: (h _  isf) => le1.
   rewrite -/(Vf f i); apply/ oleP => //; exact (proj32 le1).
rewrite cpow_pr0.
set E1 := gfunctions (omega_fct b) (omega_fct a).
have eu: sub E1  (unionb (Lg F1 (fun g => (productb (G g))))).
  move=> f; rewrite /E1 => fe.
  move: (gfunctions_hi fe) => [h [fh sh tf gh]].
  have hd: inc h E by  apply /functionsP;split => //.
  move: (pa _ hd) => [g ge gv].
  by apply /setUb_P; aw; exists g=> //; rewrite LgV//; rewrite -gh.
move: (sub_smaller eu).
set Y := Lg _ _.
have fgy: fgraph Y by rewrite /Y; fprops.
move: (csum_pr1 Y) => le1 le2; move: (cleT le2 le1).
rewrite {1}/Y; aw ;move => le3; apply: (cleT le3); clear le1 le2 le3.
set p := cprod _.
have aux: p *c F1 <=c p.
   have -> : p *c F1 = p *c (cardinal F1) by  symmetry; apply: cprod2cr.
   have ne1: cardinal F1 <> \0c.
     move/ card_nonempty; apply/nonemptyP.
     exists (identity  (omega_fct b)); apply: Zo_i. 
       apply /functionsP; apply:identity_prop.
     by move: (identity_fb  (omega_fct b)) => [].
   have s1: sub F1 F by apply: Zo_S.
   move: (sub_smaller s1); rewrite /F cpow_pr1.
   move: (CIS_aleph ob) => icb.
   rewrite (card_card (proj1 icb)) (infinite_power1_b icb) => le2.
   have le3: \2c ^c omega_fct b <=c p.
     rewrite - cprod_of_same /cst_graph /p - dx; apply: cprod_increasing; aww.
     move => x xd; rewrite !LgV//; apply: infinite_ge2; apply: CIS_aleph.
      apply: (oob _ xd).
   have le1:= cleT le2 le3.
   have icp: infinite_c p. 
     move: (cantor (proj1 icb)) => le4.
     exact (cle_inf_inf icb (cleT (proj1 le4) le3)).
   rewrite (cprod_inf le1 icp ne1).
   apply: (cleR (proj1 icp)).
suff qa: forall g, inc g F1 ->  cardinal (Vg Y g) <=c p.
   have  : csumb F1 (fun a0  => cardinal (Vg Y a0)) <=c csumb F1 (fun _ => p).
    apply: csum_increasing.
          fprops.
         rewrite /cst_graph; fprops.
      by rewrite /cst_graph; aw.
    by aw => x xf; rewrite LgV// LgV//; apply: qa.
  by rewrite csum_of_same => xx; apply:  (cleT xx).
move => g gi; rewrite /Y LgV//.
move: gi => /Zo_P [] /functionsP [fg sg tg] ig.
set f:= (Lg (omega_fct b) (fun z : Set =>  (omega_fct (Vg X (Vf g z))))).
have ->: cardinal (productb (G g)) = cprod f.
  apply:Eqc_setXb.
  rewrite /G/f; split;aww; move => x xd; rewrite !LgV //.
  have wi: inc  (Vf g x) (domain X).
     rewrite dx -tg; apply: Vf_target => //; ue.
  move /card_eqP: (proj2 (CIS_aleph (oob _ wi))).  done.
rewrite /p.
set h := Lg _ _.
move: (Imf_Starget fg) => sd1. 
move: (sd1); rewrite tg - dx => sd.
have sd2: sub (Imf g) (domain h) by rewrite /h; aw.
have ca: cardinal_fam h.
   rewrite /h/cardinal_fam; red;aw => i idx; rewrite LgV//.
   apply: CS_aleph;  exact (oob _ idx).
have -> : cprod f  = cprod (restr h (Imf g)).
  have fgh: fgraph h by rewrite /h; fprops.
  rewrite /f /h.
  move: (restriction_to_image_fb ig) => bg.
  set Z:= restr _ _.
  have fgz: fgraph Z by rewrite /Z/restr; apply: restr_fgraph. 
  have trt:  target (restriction_to_image g) = domain Z.
    by rewrite /restriction_to_image /restriction2 /Z restr_d //; aw.
  rewrite (cprod_Cn  trt bg) /composef (domain_fg (proj1 (proj1 bg))).
  rewrite {1} /restriction_to_image /restriction2; aw; rewrite sg.
  apply: f_equal; apply: Lg_exten => x xd.
  have xsd: inc x (source g) by ue.
  have wi: inc (Vf g x) (Imf g).
    apply /(Imf_P fg); ex_tac.
  have ra: restriction2_axioms g (source g) (Imf g) by split.
  rewrite -/(Vf  (restriction_to_image g) x) /restriction_to_image /Z.
  by rewrite restriction2_V //restr_ev // LgV//; apply: sd.
rewrite /h; apply: (cprod_increasing1 _ sd2).
rewrite /h;hnf; aw; move => x xd /=; rewrite LgV//;apply: aleph_nz;  exact (oob _ xd).
Qed.

Lemma exercise_6_19b a (ba := ord_index (cofinality (\aleph a)))
  (x := \aleph a) (y := \aleph ba):
  ordinalp a -> 
  (x <c x ^c y /\ 
   (forall n c, cardinalp n -> ordinalp c -> x = n ^c (\aleph c) ->
       c <o ba)).
Proof.
move => oa.
move: (CIS_aleph oa) => io.
move: (cofinality_pr3 (proj1 (proj1 io))).
move: (cofinality_infinite io).
rewrite (cofinality_card io) =>pa pd.
move: (cofinality_card io) => H.
move: (ord_index_pr1 pa) => [pb]; rewrite - /ba -/y -/x - H.
move => yc.
split.
  rewrite yc; apply: power_cofinality.
  by apply: infinite_ge2; apply: CIS_aleph.
move => n c cn oc eq.
have qa: \2c <=c n.
  apply: cge2 => //.
    move=> n0; move: eq; rewrite n0 cpow0x; by  apply: aleph_nz.
  move => n1; move:  eq; rewrite n1 cpow1x => x1.
  move: (CIS_aleph oa); rewrite -/x x1.
  apply: finite_not_infinite; fprops.
have qb:infinite_c (\aleph c) by apply: CIS_aleph.
move: (power_cofinality5 qa qb); rewrite -eq - H - yc => l2. 
apply: aleph_ltc_lt => //.
Qed.



(** ----  Exercise 6 24 *)

Section Exercise6_24.
Variables (E F a: Set).
Hypothesis FE: forall x, inc x F -> sub x E.
Hypothesis cF: cardinal F = a.
Hypothesis ceF: forall x, inc x F -> cardinal x = a.
Hypothesis iF: infinite_c a.

Lemma Exercise6_24a: 
   exists P, [/\ sub P E,cardinal (P) = a &
   forall x, inc x F -> ~ (sub x P)].
Proof.
move: (proj1 iF) => ca.
move: (sym_eq cF); rewrite - (card_card ca); move /card_eqP => [g [bg sg tg]].
have fg: function g by fct_tac.
have oa: ordinalp a by apply: OS_cardinal.
have g1: forall b, b <o a -> inc (Vf g b) F.
   move => b /(oltP oa); rewrite - sg - tg => h; Wtac.
have g2: forall x, inc x F -> exists2 b, b <o a & (Vf g b) = x.
  rewrite -tg => x xt; move: (bij_surj bg xt) => [b b1 b2]; exists b => //.
  apply /(oltP oa); ue.
pose PP x b p := [/\ pairp p, (inc (P p) ((Vf g b) -s x)),
   (inc (Q p) ((Vf g b) -s x))  & P p <> Q p].
have g3: forall x b, cardinal x <c a -> b <o a -> exists p, PP x b p.
  move => x b cx ba; rewrite /PP;move: (g1 _ ba); set s:= (Vf g b) => sF.
  have cs: cardinal s = a by apply: ceF.
  have ifs: infinite_set s by apply /infinite_setP; rewrite cs.
  rewrite - cs in cx.
  move: (infinite_compl ifs cx); rewrite cs => h.
  have: (\2c <=c cardinal (s -s x)) by apply: cle_fin_inf; fprops; ue.
  move/cle2P => [u [v [u1 u2 u3]]]. 
  exists (J u v);split => //; aww.
pose g4 x b := choose (PP x b).
have g5: forall x b, cardinal x <c a -> b <o a -> PP x b (g4 x b).
move => x b p1 p2; move: (g3 _ _ p1 p2); apply: choose_pr.
pose mu X := (domain X \cup range X).
have mu1: forall X, cardinal X <c a -> cardinal (mu X) <c a.
  move => X xs; apply: csum2_pr6_inf2 => //;
  apply: cle_ltT xs; apply: fun_image_smaller.
pose g6 fct := g4 (mu (target fct)) (source fct).
move: (ordinal_o_wor oa) => wor.
move: (transfinite_defined_pr g6 wor).
set f := transfinite_defined _ _.
rewrite /transfinite_def (ordinal_o_sr a); move=> [pa pb pc].
have g7: forall x, inc x a -> Vf f x = g4 (mu (Vfs f x)) x.
  by move => x xa; rewrite (pc _ xa) 
    (ordinal_segment oa xa) /g6 /restriction1; aw.
have g8: forall x, inc x a -> cardinal x <c a.
  move => x /(oltP oa) h.
  apply /(ocle2P ca) => //; exact: (proj31_1 h).
have g9: forall x, inc x a ->  PP (mu (Vfs f x)) x  (Vf f x).
   move => x xa.
   have: x <o a by apply /oltP.
   rewrite (g7 _ xa); apply: g5; apply: mu1; apply: (cle_ltT  _ (g8 _ xa)). 
   exact: (image_smaller1 x (proj1 pa)).
pose f1 z:= P (Vf f z).
have g10: forall z, inc z a -> inc (f1 z) E.
  move => z za; move: (g9 _ za) => [_ /setC_P [h _] _ _]; apply: FE h.
  by apply: g1; apply /(oltP oa).
have aT: forall s, inc s a -> sub s (source f).
  by move => s sa; rewrite pb; apply: ordinal_transitive.
set r := fun_image a f1.
have r1: sub r E by move => t /funI_P [z za ->]; apply g10.
have r2: cardinal r = cardinal a.
  symmetry; apply/card_eqP; exists (Lf f1 a r); aw. 
    saw;apply: lf_bijective.
        move => t ta; apply /funI_P; ex_tac.
     suff: forall u v, u <o v -> inc v a -> f1 u <> f1 v.
      move => H u v ua va sf.
      have ou:= Os_ordinal oa ua.
      have ov:= Os_ordinal oa va.
      case: (oleT_ell ou ov) => // l1.
        by case: (H _ _ l1 va).
        by case: (H _ _ l1 ua).
    move => u v uv va sv; move: (g9 _ va) => [_ /setC_P [sa sb] _ _ ].
    case: sb; rewrite -/(f1 v) - sv; apply /setU2_P; left; apply /funI_P.
    have iuv:= olt_i uv.
    exists (Vf f u) => //; apply /(Vf_image_P (proj1 pa));fprops;last by ex_tac.
  by move => y /funI_P.
exists r ;split => //.
move => x; rewrite - tg => xtg; move: (bij_surj bg  xtg); rewrite sg.
move => [z za ->] bad.
move: (g9 _ za) => [_ _ /setC_P [f2g f2r]] f1f2.
move: (bad _ f2g) => /funI_P [s sa sb].
have oz:= Os_ordinal oa za.
have os:= Os_ordinal oa sa.
case: (oleT_ell oz os);  move => zs; first by case: f1f2; rewrite sb zs.
  move: (g9 _ sa) => [_]; rewrite -/(f1 s).
  move => /setC_P [_ f1r'] _.
  case: f1r'; rewrite - sb; apply /setU2_P; right; apply /funI_P.
  have iuv:= olt_i zs.
  exists (Vf f z) => //; apply /(Vf_image_P (proj1 pa)); fprops; by ex_tac.
case: f2r; rewrite sb; apply /setU2_P; left; apply /funI_P.
have iuv:= olt_i zs.
exists (Vf f s) => //; apply /(Vf_image_P (proj1 pa));fprops;last by ex_tac.
Qed.

Lemma Exercise6_24b:  
   (forall G, sub G F -> cardinal G <c a ->
       a <=c cardinal (E -s union G)) ->
   exists P, [/\ sub P E, cardinal (P) = a &
   forall x, inc x F -> (cardinal (P \cap x)) <c a].
move: (proj1 iF) => ca.
move: (sym_eq cF); rewrite - {1 4} (card_card ca). 
move /card_eqP => [g [bg sg tg]].
have fg: function g by fct_tac.
have oa: ordinalp a by apply: OS_cardinal.
have g1: forall b, b <o a -> inc (Vf g b) F.
   move => b /(oltP oa); rewrite - sg - tg => h; Wtac.
have g2: forall x, inc x F -> exists2 b, b <o a & (Vf g b) = x.
  rewrite -tg => x xt; move: (bij_surj bg xt) => [b b1 b2]; exists b => //.
  apply /(oltP oa); ue.
move => bighyp.
pose PP x b p :=  [/\ inc p E, ~ inc p x & ~ inc p (unionf b (Vf g))].
have g3: forall x b, cardinal x <c a -> b <o a -> exists p, PP x b p.
   move => X z cx za; rewrite /PP.
   set G := (fun_image z (Vf g)).
   have sza:= proj33 (proj1 za).
   have sG: sub G F. 
       move => t /funI_P [s sa ->]; apply: g1.  
       apply /(oltP oa); exact(sza s sa).
   have oz:= proj31_1 za.
   move /(ocle2P ca oz): za => lt1.
   have cG: cardinal G <c a.
       apply: cle_ltT lt1; apply: (fun_image_smaller).
   move: (bighyp _ sG cG) => le1.
   move: (clt_leT cx le1) => le2.
   have ifs: infinite_set (E -s union G).
     by apply /infinite_setP;apply: (cle_inf_inf iF le1).
   move: (infinite_compl ifs le2) => le3.
   case: (emptyset_dichot ((E -s union G) -s X)) => ee.
   move: ifs => /infinite_setP; rewrite -le3 ee cardinal_set0 => le4.
   case: (finite_not_infinite finite_0 le4).
   move: ee => [x /setC_P [/setC_P [xe xg]] xX]; ex_tac => //  xu; case: xg.
   move /setUf_P: xu => [y ya yb]; apply /setU_P; exists (Vf g y)=> //.
   apply /funI_P; ex_tac.
pose g4 x b := choose (PP x b).
have g5: forall x b, cardinal x <c a -> b <o a -> PP x b (g4 x b).
  move => x b p1 p2; move: (g3 _ _ p1 p2); apply: choose_pr.
pose g6 fct := g4 (target fct) (source fct).
move: (ordinal_o_wor oa) => wor.
move: (transfinite_defined_pr g6 wor).
set f := transfinite_defined _ _.
rewrite /transfinite_def (ordinal_o_sr a); move=> [pa pb pc].
have g7: forall x, inc x a -> Vf f x = g4 (Vfs f x) x.
  by move => x xa; rewrite (pc _ xa) 
    (ordinal_segment oa xa) /g6 /restriction1; aw.
have g8: forall x, inc x a -> cardinal x <c a.
  move => x /(oltP oa) h.
  by apply /(ocle2P ca (proj31_1 h)).
have g9: forall x, inc x a ->  PP (Vfs f x) x  (Vf f x).
   move => x xa.
   have: x <o a by apply /oltP.
   rewrite (g7 _ xa); apply: g5; apply: (cle_ltT  _ (g8 _ xa)). 
   exact: (image_smaller1 x (proj1 pa)).
have aT: forall s, inc s a -> sub s (source f).
  by move => s sa; rewrite pb; apply: ordinal_transitive.
exists (target f);split => //.
    by move => t /(proj2 pa); rewrite pb; move => [x /g9 [xe _ _]] ->.
   symmetry; apply /card_eqP; exists f; saw; split => //. 
   split; first by fct_tac.
   suff: forall u v, u <o v -> inc v a -> (Vf f u) <> Vf f v.
     rewrite pb => H x y xsf ysf sv.
     have ox:= Os_ordinal oa xsf.
     have oy:= Os_ordinal oa ysf.
     case:(oleT_ell ox oy) => // h.
      by case: (H _ _ h ysf).
      by case: (H _ _ h xsf).
  move => u v uv va sv; move: (g9 _ va) => [_ h1 _].
  have ov:= proj32_1 uv.
  move /(oltP ov): uv => uv1.
  case: h1; rewrite - sv; apply /(Vf_image_P (proj1 pa)); fprops; ex_tac.
move => x; rewrite -tg => xtg; move: (bij_surj bg xtg); rewrite sg.
move => [b ba ->]; set G := _ \cap _.
have: sub G (fun_image (osucc b) (fun z => Vf f z)).
  move => t /setI2_P [/(proj2 pa)]; rewrite pb; move => [z za ->] zb.
  move:(g9 _ za) => [_ h1 h2].
  have oz:= Os_ordinal oa za.
  have ob:= Os_ordinal oa ba.
  apply /funI_P; exists z => //.
  case:(oleT_ell oz ob) => // h.
      rewrite h; fprops.
    by apply /setU1_P; left; apply /oltP.
  by case: h2; apply /setUf_P; exists b => //; apply /oltP.
move /sub_smaller => h1; apply: (cle_ltT h1).
  apply: (@cle_ltT (cardinal (osucc b))). 
    by apply:fun_image_smaller.
  move: (infinite_card_limit2 iF) => [_ _ h]. 
  move: (h _ ba) => /(oltP oa) lt1.
  apply /(ocle2P ca) => //; exact (proj31_1 lt1).
Qed.

End Exercise6_24.


End Exercise5.




