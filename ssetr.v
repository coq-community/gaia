(** * The set R of real numbers
  Copyright INRIA (2014-2015 2018) Marelle Team (Jose Grimm).
*)
(* $Id: ssetr.v,v 1.4 2018/09/04 07:58:00 grimm Exp $ *)

Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Warnings "notation-overridden".

Require Export sset10 ssetq2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module RealNumbers.
(** ** The set of real numbers *)


(** ** Dedekind cuts *)

Definition or_cut r B := 
   sub B (substrate r) /\ (forall x y, inc x B -> glt r x y -> inc y B).
Definition or_cuts r := Zo (powerset (substrate r)) (or_cut r).
Definition or_cut_order r := opp_order (sub_order (or_cuts r)).

Lemma or_cutsP r B: inc B (or_cuts r) <-> (or_cut r B).
Proof.
split; [ by move/Zo_hi | move => h; apply:Zo_i => //].
by move:h => [/setP_P].
Qed.

Lemma or_cut_osr r: order_on (or_cut_order r) (or_cuts r).
Proof.
have [or sr]:=(sub_osr (or_cuts r)).
by move: (opp_osr or); rewrite sr.
Qed.


Lemma or_cut_tor r: total_order r -> total_order (or_cut_order r).
Proof.
move: (or_cut_osr r) => [or sr] tor.
split => // x y; rewrite sr => xc yc.
suff: sub x y \/ sub y x.
   by case => h; [right | left]; apply/opp_gleP; apply/sub_gleP.
move/or_cutsP: xc => [xsr cx].
move/or_cutsP: yc => [ysr cy].
case(p_or_not_p (sub x y)) => h; first by left.
have[a ax nay]: exists2 a, inc a x & ~inc a y.
   ex_middle bad; case h => b bx; ex_middle iby; case bad; ex_tac.
right => b iby.
case: (equal_or_not a b) => eab; first by case:nay; rewrite eab.
case: (proj2 tor _ _ (xsr _ ax) (ysr _ iby)).
  by move => lab; move:(cx _ _ ax (conj lab eab)).
move => lab; case: nay; exact: (cy b a iby (conj lab (nesym eab))).
Qed.

Lemma or_cut_gleP r x y:
   gle (or_cut_order r) x y <-> [/\ ( or_cut r x),  or_cut r y & sub y x].
Proof.
split.
  by move/opp_gleP => /sub_gleP [/or_cutsP sa /or_cutsP sb sc]; split.
by move => [/or_cutsP sa /or_cutsP sb sc]; apply/opp_gleP /sub_gleP.
Qed.

Lemma or_cut_gle_least r : least (or_cut_order r) (substrate r) .
Proof.
have [or sr]:= (or_cut_osr r).
have pc: or_cut r (substrate r) by split => // x y _ h; order_tac.
have pf:inc (substrate r) (or_cuts r) by apply/or_cutsP.
by hnf;rewrite sr; split => // x /or_cutsP [xsrp xp]; apply/ or_cut_gleP. 
Qed.

Lemma or_cut_gle_greatest r : greatest (or_cut_order r) emptyset.
Proof.
have [or sr]:= (or_cut_osr r).
have pc: or_cut r emptyset by split => x; [move/in_set0 | move => y /in_set0].
have pf:inc emptyset (or_cuts r)  by apply/or_cutsP.
hnf;rewrite sr; split => // x /or_cutsP xc; apply/ or_cut_gleP; split => //.
exact:sub0_set.
Qed.


Lemma or_cut_P r B : sub B (substrate r) ->
    (or_cut r B <-> segmentp r (substrate r -s B)).
Proof.
move=> bsr; split.
  move => [_ sb]; split; first by move => t/setC_P [].
  move => x y /setC_P [xset nxB] lexy; apply/setC_P; split => //.
    order_tac.
  dneg yb; apply: (sb y) => //;split => // exy; case:nxB; ue. 
move => [sa sb]; split => // x y xb [ha hb]; ex_middle nxb.
have hc: inc y  (substrate r -s B) by apply/setC_P; split => //; order_tac.
by move:(sb _ _ hc ha) => /setC_P [_].
Qed.

Lemma or_cut_prop2 r B : order r ->  sub B (substrate r) ->
   (forall x y, inc x (substrate r -s B) -> inc y B -> glt r x y) -> 
    or_cut r B.
Proof.
move => or sa sb; split => // x y xb lxy; ex_middle xne.
have h: inc y ((substrate r) -s B) by apply/setC_P; split => //; order_tac.
move:(sb y x h xb)=> [ha _]; order_tac.
Qed.

Lemma or_cut_P2 r B : total_order r -> sub B (substrate r) ->
  (or_cut r B <-> forall x y, inc x (substrate r -s B) -> inc y B -> glt r x y).
Proof.
move => [or tor] sa; split; last by apply/or_cut_prop2.
move => [ua ub] x y /setC_P[xsr nb] yb.
have nxy: x <> y by dneg h; ue.
case: (tor _ _ xsr (sa _ yb)) => ha; first by split.
case:nb; exact: (ub y x yb (conj ha (nesym nxy))).
Qed.

Lemma or_cut_segment r x : order r ->
   or_cut r (Zo (substrate r) (fun t => glt r x t)).
Proof.
move => or;split; first by apply:Zo_S.
move => a b /Zo_P[_ lxa lab]; apply/Zo_P; split; order_tac. 
Qed.


Lemma or_cut_segmente r x : order r -> 
   or_cut r (Zo (substrate r) (fun t => gle r x t)).
Proof.
move => or;split; first by apply:Zo_S.
move => a b /Zo_P[_ lxa [lab _]]; apply/Zo_P; split; order_tac. 
Qed.

Lemma or_cut_segment_cp r x y
  (X :=  Zo (substrate r) (fun t => glt r x t))
  (Y :=  Zo (substrate r) (fun t => glt r y t)):
  total_order r -> inc x (substrate r) -> inc y (substrate r) ->
  (glt r x y <-> glt (or_cut_order r) X Y). 
Proof.
move => [or tor] xsr ysr;split. 
  move => lxy; split.
    apply/or_cut_gleP; split.
    + apply:(or_cut_segment _ or).
    + apply:(or_cut_segment _ or).
    + move => t /Zo_P [ta tb]; apply/Zo_P; split => //; order_tac.
  move=> eXY.
  have: inc y X by apply:Zo_i. 
  by rewrite eXY; move /Zo_hi => [_].
move => [/or_cut_gleP [[sa sb] [sc sd]] se] XY. 
have xy: x <> y by  dneg h; rewrite /X/Y h.
split => //; case: (tor _ _ xsr ysr) => // cxy.
have: inc x Y by apply:Zo_i => //; split => //; apply:nesym.
by move/se => /Zo_hi [_].
Qed.

Lemma or_cut_segmente_cp r x y
  (X :=  Zo (substrate r) (fun t => gle r x t))
  (Y :=  Zo (substrate r) (fun t => gle r y t)):
  total_order r -> inc x (substrate r) -> inc y (substrate r) ->
  (glt r x y <-> glt (or_cut_order r) X Y).
Proof.
move => [or tor] xsr ysr;split.
  move => [lxy nxy]; split.
    apply/or_cut_gleP; split.
    + apply:(or_cut_segmente _ or).
    + apply:(or_cut_segmente _ or).
    + move => t /Zo_P [ta tb]; apply/Zo_P; split => //; order_tac.
  dneg eXY.
  have: inc x X by apply /Zo_P; split => //; order_tac.
  rewrite eXY; move /Zo_hi => ha; order_tac.
move => [/or_cut_gleP [[sa sb] [sc sd]] se] XY. 
have xy: x <> y by  dneg h; rewrite /X/Y h.
split => //; case: (tor _ _ xsr ysr) => // cxy.
have: inc y Y by apply /Zo_P; split => //; order_tac.
move/se => /Zo_hi ha; case xy; order_tac.
Qed.

Lemma or_cut_segment_irrelevant r x Y
  (X :=  Zo (substrate r) (fun t => glt r x t))
  (X' :=  Zo (substrate r) (fun t => gle r x t)):
  order r -> Y <> X -> Y <> X' ->   
 (glt (or_cut_order r) X Y <-> glt (or_cut_order r) X' Y).
Proof.
move => or ha hb. 
move: (or_cut_segment x or)(or_cut_segmente x or).
rewrite -/X -/X' => cx xy.
split;move => [/or_cut_gleP [sa sb sc] sd]; split.
+ apply/or_cut_gleP; split => // t ty.
  by move: (sc _ ty) => /Zo_P [tst [lxt _]]; apply:Zo_i.
+ by apply:nesym. 
+ apply/or_cut_gleP; split => // t ty.
  case: (inc_or_not x Y) => xY.
    case hb; apply: extensionality => // z zX.
    case: (equal_or_not x z) => exz; first by rewrite - exz.
    by move/Zo_P:zX => [za zb]; move: sb => [_ hh]; apply: (hh _ _ xY).
  move: (sc _ ty) => /Zo_P [tsr lxt]; apply/Zo_P; split => //; split => //.
  by dneg h; rewrite h.
+ by apply:nesym.
Qed.


Lemma or_cut_supinf r X:
  order r -> (forall x, inc x X -> or_cut r x) ->
  (or_cut r (union X) /\ or_cut r (intersection X)).
Proof.
move => sa sb; split.
  split; first by apply: setU_s2 => y /sb [].
  move => x y /setU_P [z za zb] zc; apply/setU_P; ex_tac.
  by move:(sb _  zb) => [ca cb]; apply: (cb _ _ za zc).
case: (emptyset_dichot X) => xE.
  move:(proj1 (or_cut_gle_greatest r)).
  by rewrite (proj2 (or_cut_osr r)) xE setI_0; move => /Zo_hi.
move:(xE) => [u uX].
split; first by move => t ti; exact:(proj1 (sb _ uX) _  (setI_hi ti uX)).
move => x y xi h; apply/(setI_P xE) => z zX. 
have xz: inc x z by move/(setI_P xE):xi => H; apply:H.
exact:(proj2 (sb _ zX) x y xz h).
Qed.


Definition real_dedekind B :=
   [/\ sub B  BQ, nonempty B, B <> BQ, 
      (forall x y, inc x B -> x <q y -> inc y B) &
      (forall x, inc x B -> exists2 y, inc y B & y <q x)].

Definition irrationalp B :=  real_dedekind B /\
  (forall x, inc x (BQ -s B) -> exists2 y , inc y (BQ -s B) & x<q y).

Definition rationalp x := real_dedekind x /\ ~ (irrationalp x).

Definition BR_of_Q x := Zo BQ (fun z => x <q z).


Lemma BR_of_Q_prop1 x: ratp x -> rationalp (BR_of_Q x).
Proof.
move => xq; set E := (BR_of_Q x).
have pa: inc x (BQ -s E) by apply /setC_P; split => // /Zo_P [_][].
split; last first.
   move => [_ h]; move: (h x pa) => [y /setC_P [ya yb] yc].
   by case: yb; apply: Zo_i.
have H: forall y, x <q y -> inc y E. 
  move => y yy; apply:Zo_i=> //;exact:(proj32_1 yy).
split.
+ by apply: Zo_S.
+ by exists (x +q \1q); apply:H; apply: qlt_succ.
+ move => h; move: pa; rewrite h setC_v; case; case.
+ move => y z /Zo_P [pb pc] pd; apply: H; BQo_tac.
+ move => y /Zo_P[ya /BQmiddle_comp [yb yc]].
  by exists (BQmiddle x y) => //; apply:H.
Qed.

Lemma BR_of_Q_prop2 X: rationalp X ->
  exists2 x, ratp x & X = BR_of_Q x.
Proof.
move => [pu pf]; ex_middle h; case: pf; split => // x /setC_P [xq nxX].  
move:pu => [pa pb pc pd pe]. 
ex_middle h2;case: h; exists x => //.
have ha: forall y, inc y (BQ -s X) -> y <=q x.
  move => y yu;move/setC_P: (yu) => [yq _].
  case:(qleT_el yq xq) => // h; case: h2; ex_tac.
set_extens t.
  move => tx; apply/Zo_P; split => //; first by apply: pa.
  case:(qleT_el (pa _ tx) xq) => // tb;case: nxX. 
  by case: (equal_or_not t x) => etx; [rewrite - etx | apply:(pd _ _ tx)].
move => /Zo_P [tq xt]; ex_middle tne; move:(ha _ (setC_i tq tne)) => hb.
BQo_tac.
Qed.

Lemma BR_of_Q_inj1: {inc BQ &, injective BR_of_Q}.
Proof.
move => u v uq vq eq.
case: (qleT_ell uq vq) => lt.
+ exact.
+ have: inc v (BR_of_Q u) by apply:Zo_i.
  by rewrite eq=> /Zo_hi [_].
+ have: inc u (BR_of_Q v) by apply:Zo_i.
  by rewrite - eq=> /Zo_hi [_].
Qed.

Definition BQ_of_R x := (select (fun y => x = BR_of_Q y) BQ).

Lemma BQ_of_R_prop x: rationalp x ->
  x =  BR_of_Q (BQ_of_R x) /\ inc (BQ_of_R x) BQ.
Proof.
move => /BR_of_Q_prop2 Ha.
have Hb:singl_val2 (inc^~ BQ) (fun y => x = BR_of_Q y).
   by move => u v /= uq eq1 vq; rewrite eq1;apply: BR_of_Q_inj1.
exact: (select_pr Ha Hb). 
Qed.

Lemma BQ_of_R_prop2 x: ratp x -> BQ_of_R (BR_of_Q x) = x.
Proof.
move => H; symmetry.
have [sa sb]:=(BQ_of_R_prop (BR_of_Q_prop1 H)).
by move/(BR_of_Q_inj1 H sb): sa.
Qed.

Definition BRsqrt2 := (Zo BQps (fun z => \2q <q z *q z)).

Lemma sqrt2_irrational: irrationalp BRsqrt2. 
Proof.
have sw:=BQ_square_2.
have sa:= qlt_12.
have sc:= QpsS2.
split; first split.
+ by move => t /Zo_S /BQps_sBQ.
+ exists \2q; apply:Zo_i; first apply: QpsS2. 
  by move:(BQprod_Mltgt0  QpsS2 qlt_12); rewrite (BQprod_1l QS2).
+ by move => h; move: QS0; rewrite /ratp -h => /Zo_S => /BQps_iP [ _]. 
+ move => x y /Zo_P [pa pb] pc; apply: Zo_i.
   apply / qlt0xP; move/ qlt0xP: pa => pd; BQo_tac.
   move:(BQprod_Mltltge0 (BQps_sBQp pa) (BQps_sBQp pa) pc pc) => pd; BQo_tac.
+ move => x  /Zo_P [pa pb].
  set y := (x *q x +q \2q) /q (\2q *q x).
  have ya:=(QpsS_prod sc pa).
  have xq:= (BQps_sBQ pa).
  have yb:= (QpsS_sum_rl(QpsS_prod pa pa) sc).
  have ybb := (BQps_sBQ yb).
  have yc:= (QSp xq xq).
  have yd: inc y BQps by apply: QpsS_div. 
  have ye:=(QS_diff yc QS2).
  have yf:= (BQps_sBQ ya).
  set z := (x*q x -q \2q) /q (\2q *q x).
  move: (QpsS_prod ya ya) =>  /BQps_iP [ _ yg].
  have yh : BQsquare y = \2q +q (BQsquare z).
     rewrite (BQdiv_square ybb yf)(BQdiv_square ye yf). 
     rewrite (BQsum_div QS2 (QSp ye ye) (QSp yf yf) yg).
     rewrite (BQsumdiff_square (QSp xq xq) QS2).
     rewrite -BQprod_22 (BQprodA (QSp QS2 QS2) yc QS2).
     by rewrite (BQprod_ACA QS2 QS2 xq xq) (BQprodC _ \2q).
  have yi: y <q x. 
    rewrite - (BQdiv_x1 xq).
    apply /(BQdiv_Mltltge0 ybb ya xq QpsS1); rewrite (BQprod_1r ybb).
    rewrite - (BQprodA QS2 xq xq) - /(BQdouble _) - (BQdouble_p yc).
    by apply/(BQsum_lt2l QS2 yc yc).
  have zp: inc z BQps by apply:QpsS_div => //; apply/ (qlt_diffP QS2 yc).  
  have yj: \2q <q y *q y.  
     rewrite -/(BQsquare _) yh;apply: (BQsum_Mps QS2);apply:(QpsS_prod zp zp).
  exists y; [ by apply/Zo_P | exact].
+ move => x /setC_P [xq xp]; case/BQ_i2P: xq; last first.
    move => / qge0xP xn; move:(qle_ltT xn qlt_01) => x1; exists \1q => //.
    apply /setC_P; split; [exact:QS1 | apply/ Zo_P].
    rewrite (BQprod_1l QS1); move => [_ [h _]]; BQo_tac.
  move => xpo; move /Zo_P: (xpo)=> [xq ap].
  case: (qleT_ell QS2 (QSp xq xq)).
  - by move => h; case:(sw _ xq).
  - by move => h; case: xp; apply/ Zo_P.
  - rewrite -/(BQsquare _); move: (BQ_squarep xq) => ->.
  rewrite {1} /BQ_two /BQ_of_Z; move/ qltP => [ _ _]; aw.
  move /BQ_P: (xq); set a := P x; set b := Q x.
  move => [_ az bz _]; rewrite (BZprod_1r (ZSp az az)) => eq1.
  move /(zlt_succ2P  (proj31_1 eq1) (proj32_1 eq1)): eq1 => eq2.
  move:(BQdiv_numden xq); rewrite -/a -/b.
  set a' := BQ_of_Z a; set b' := BQ_of_Z b => xv.
  have a'qps:=(BQ_of_Z_iQps ap).
  have b'qps:=(BQ_of_Z_iQps bz).
  move /BQps_iP:(a'qps) => [ /BQp_sBQ a'q a'nz].
  have b'q:= BQps_sBQ b'qps.
  set yn := a' +q BQinv (\4q *q a').
  set y := BQdiv yn b'.
  have p4z:= BZprod_22.
  have ha0 := (QpsS_prod QpsS4 a'qps). 
  have hf:=BQps_sBQ ha0.
  have ha:= (QpsS_inv ha0). 
  have ha' := BQps_sBQ ha.
  have ynq: ratp yn by apply:QSs.
  have yq: ratp y by apply:QS_div.
  have lt1: x <q y.
    rewrite /y /yn (BQdiv_sumDl b'q a'q ha') xv; apply: BQsum_Mps => //.
    by apply:QpsS_div.
  suff ly2: BQsquare y <=q \2q.
     exists y => //;apply/setC_P; split => // /Zo_P [_ y2]; BQo_tac.
  rewrite (BQdiv_square ynq b'q). 
  apply/ (BQdiv_Mle1 (QSp ynq ynq) QS2 (QpsS_prod b'qps b'qps)).
  move /(qle_cZ (proj31 eq2) (proj32 eq2)): eq2.
  have bz0 := (BZps_sBZ bz).
  have bbz:= (ZSp bz0 bz0).
  rewrite (BQprodC \2q) - (BQprod_cZ bbz ZS2) - (BQprod_cZ bz0 bz0).
  apply: qleT;rewrite - (BQsum_cZ (ZSp az az) ZS1) -/BQ_one.
  move: (QSp a'q a'q) (QSp ha' ha') (QSp QS2 (QSp a'q ha')) => hb hc hd.
  rewrite -(BQprod_cZ az az) -/a' /yn -/(BQsquare _)(BQsum_square a'q ha').
  rewrite - (BQsumA hb hc hd); apply/(BQsum_le2l (QSs hc hd) QS1 hb).
  have he := (BQps_sBQ QpsS4).
  have hg:= (QS_inv he).
  have sp4s:=BZps_sBZp ZpsS4.
  have hi:=(ZSp ZS4 az).
  have ->: \2q *q (a' *q BQinv (BQ_of_Z \4z *q a')) = \2hq.
     rewrite (BQprodC _ a') (BQprod_inv a'q he).
     rewrite (BQprodA a'q (QS_inv a'q) hg)(BQprod_inv1 a'q a'nz)(BQprod_1l hg).
     rewrite -BQprod_22 (BQprod_inv QS2 QS2).
     by rewrite  (BQprod_div QS2 (QS_inv QS2) BQ2_nz) BQinv_2.
  rewrite - BQdouble_half2; apply/(BQsum_le2r hc QSh2 QSh2).
  rewrite - (BQprod_inv hf hf) - (BQdiv_1x (QSp hf hf)) - BQinv_2.
  rewrite -(BQdiv_1x QS2); apply/(BQinv_mon (QpsS_prod ha0 ha0) QpsS2).
  rewrite (BQprod_cZ ZS4 az) (BQprod_cZ hi hi).
  apply/(qle_cZ ZS2 (ZSp hi hi)).
  have hj: \4z <=z (\4z *z a) by apply:BZprod_Mpp.
  move:(BZprod_Mlege0 (BZps_sBZp (ZpsS_prod ZpsS4 ap)) (zleT zle_24 hj)).
  apply: zleT; apply:BZprod_Mpp (BZps_sBZp ZpsS2) (ZpsS_prod ZpsS4 ap).
Qed.


Definition BR := Zo (powerset BQ) real_dedekind.
Definition realp x := inc x BR.

Definition BR_order := opp_order (sub_order BR).
Definition BR_le x y := [/\ realp x, realp y  & sub y x].
Definition BR_lt x y :=  BR_le x y /\ x <> y.

Notation "x <=r y" := (BR_le x y) (at level 60).
Notation "x <r y" := (BR_lt x y) (at level 60).

Lemma BR_P x: realp x <-> real_dedekind x.
Proof.
split; first by move => /Zo_hi. 
by move => h;apply: Zo_i => //; apply/setP_P;move: h => [].
Qed.

Lemma BRi_sQ x: realp x -> sub x BQ.
Proof. by  move/Zo_P => [/setP_P]. Qed.

Lemma BRi_segment x y z :realp x -> inc y x -> y <q z -> inc z x. 
Proof. move /BR_P => [_ _ _ pd _]; apply: pd. Qed.

Lemma BRi_no_lowbound x y: realp x -> inc y x -> exists2 z, inc z x & z <q y. 
Proof. move /BR_P => [_ _ _  _]; apply. Qed.


Lemma BRi_lowbound x d: realp x -> inc d BQps ->
   exists2 y, inc y x & forall z, inc z x -> y -q d <q z.
Proof.
move => xr dps; move: (BQps_sBQ dps) => dq.
move/BR_P:(xr) => [pa pb pc pd pe].
move:(pb) (setC_ne (conj pa pc)) => [a ax] [b /setC_P [bq bnx]].
have aq:=(pa _ ax).
case:(qleT_ell aq bq) => lab; first by case:bnx; rewrite - lab.
   by case:bnx; apply: (pd _ _ ax).
move/(qlt_diffP1 bq aq): lab => / qlt0xP dp.
have qq:=(QpsS_div dp dps).
have [n nN lt1]:=(BQ_floorp4 ((BQps_sBQ qq))).
pose prop m :=  ~inc (a -q (BQ_of_nat m) *q d) x.
have prop3: prop n.
  move /(BQprod_plt2r (proj31_1 lt1) (proj32_1 lt1) dps): lt1.
  rewrite BQprodC (BQprod_div dq (BQps_sBQ dp) (BQps_nz dps)) => h1.
  move/(BQdiff_lt1P aq bq (proj32_1 h1)): h1 => h2.
  by move => h; case: bnx; apply:(pd _ _ h).
case:(least_int_prop2 nN prop3).
  by rewrite /prop (BQprod_0l dq)(BQdiff_0r aq);move => [].
set m := cpred _;move => [mN ma /excluded_middle]; set c:= (a -q _) => cx.
have ncx: ~ (inc (c -q d) x).
  move:(BZ_of_nat_i mN) => sa; move:(BQ_of_Z_iQ sa) => sb. 
  have pq:=(QSp sb dq).
  move: ma; rewrite /prop (Nsucc_rw mN) /BQ_of_nat - (BZsum_cN mN NS1).
  rewrite - (BQsum_cZ sa ZS1) (BQprodDl dq sb QS1) (BQprod_1l dq).
  by rewrite BQdiff_diff2.
ex_tac.
move => z zx.
have cq:=(pa _ cx); have ddq:=(QS_diff cq dq).
case: (qleT_ell ddq (pa _ zx)).
+ by move => eq; case: ncx; rewrite eq.
+ exact.
+ move => leq; case: ncx; apply:(pd _ _ zx leq).
Qed.

Lemma BR_rational_dichot x: realp x ->
    rationalp x \/ irrationalp x.
Proof.
move => /BR_P rx; case: (p_or_not_p (irrationalp x)); [ by right| by left].
Qed.

Lemma RS_of_Q x: ratp x -> realp (BR_of_Q x).
Proof. move => h; apply/BR_P;apply: (proj1 (BR_of_Q_prop1 h)). Qed.

Lemma BR_of_Q_inj: injection_prop (Lf (BR_of_Q) BQ BR) BQ BR. 
Proof.
hnf; aw; split => //; apply: (lf_injective RS_of_Q BR_of_Q_inj1).
Qed.


Definition BR_zero := BR_of_Q \0q.
Definition BR_one := BR_of_Q \1q.
Definition BR_two := BR_of_Q \2q.
Definition BR_three := BR_of_Q \3q.
Definition BR_four := BR_of_Q \4q.
Definition BR_mone := BR_of_Q \1mq.
Definition BR_half := BR_of_Q \2hq.

Notation "\0r" := BR_zero.
Notation "\1r" := BR_one.
Notation "\2r" := BR_two.
Notation "\3r" := BR_three.
Notation "\4r" := BR_four.
Notation "\1mr" := BR_mone.
Notation "\2hr" := BR_half.

Lemma RS0 : realp \0r.
Proof. by apply: RS_of_Q; apply:QS0. Qed.

Lemma RS1 : realp \1r.
Proof. by apply: RS_of_Q; apply:QS1. Qed.

Lemma RS2 : realp \2r.
Proof. by apply: RS_of_Q; apply:QS2. Qed.

Lemma BR2_nz : \2r <> \0r.
Proof. move /(BR_of_Q_inj1 QS2 QS0); apply: BQ2_nz. Qed.

Definition BRp := Zo BR (fun z => sub z BQp).
Definition BRps := BRp -s1 \0r.
Definition BRms := BR -s BRp.
Definition BRm := BR -s BRps.


Lemma BRp_sBR : sub BRp BR.       Proof. apply: Zo_S. Qed.
Lemma BRps_sBR : sub BRps BR.     Proof. by move => t/Zo_S /Zo_S. Qed.
Lemma BRms_sBR : sub BRms BR.     Proof. apply: Zo_S. Qed.
Lemma BRm_sBR : sub BRm BR.       Proof. apply: Zo_S. Qed.
Lemma BRps_sBRp : sub BRps BRp.   Proof.  apply: Zo_S. Qed.

Lemma BRms_sBRm : sub BRms BRm.
Proof. 
by move => t  /setC_P [pa pb]; apply /setC_P; split => // /setC_P [].
Qed.

Lemma RmS0: inc \0r BRm.
Proof. by apply/setC_P; split; [ apply:RS0 | move =>/setC1_P [_]]. Qed.

Lemma RpS0: inc \0r BRp.
Proof. by apply/Zo_P; split;[ apply: RS0 | move  => t /Zo_hi [] / qle0xP]. Qed.

Lemma BR_i0P x: realp x <-> (inc x BRms \/ inc x BRp).
Proof.  
split; [move => ha | case; [apply:BRms_sBR | apply:BRp_sBR ]].
by case: (inc_or_not x BRp) => h; [ right | left;apply/setC_P].
Qed.

Lemma BR_i1P x: realp x  <-> [\/ x = \0r, inc x BRps | inc x BRms].
Proof.
split. 
  move => h; case: (equal_or_not x \0r) => xz; first by constructor 1.
  case: (inc_or_not x BRp) => xp; first by constructor 2; apply/setC1_P.
  by constructor 3; apply /setC_P.
case;[ move ->; apply:RS0 | apply:BRps_sBR | apply:BRms_sBR ].
Qed.

Lemma BR_i2P x: realp x <-> (inc x BRps \/ inc x BRm).
Proof.
split; last by case; [apply:BRps_sBR | apply:BRm_sBR ].
by case/BR_i1P => h;
  [ right; rewrite h; apply:RmS0 | left | right; apply: BRms_sBRm] => //.
Qed.

Lemma BR_di_neg_pos x: inc x BRms -> inc x BRp -> False.
Proof. by move => /setC_P [_]. Qed.

Lemma BR_di_pos_neg x: inc x  BRps -> inc x BRm -> False.
Proof. by move => h /setC_P [_ ].  Qed.

Lemma BR_di_neg_spos x: inc x BRms -> inc x BRps -> False.
Proof. 
move => xn' xp; move:(BRms_sBRm xn') =>xn; apply:BR_di_pos_neg xp xn.
Qed.

Lemma BRms_nz  x: inc x BRms -> x <> \0r.
Proof. 
move /setC_P => [_ nxp] x0; case: nxp; rewrite x0; apply: RpS0.
Qed.

Lemma BRps_nz  x: inc x BRps -> x <> \0r.
Proof. by case/setC1_P. Qed.

Lemma BRps_iP x: inc x BRps <-> inc x BRp /\ x <> \0r.
Proof. exact : setC1_P. Qed.

Lemma BRms_iP x: inc x BRms <-> inc x BRm /\ x <> \0r.
Proof. 
split; first by move => h; split; [ by apply:BRms_sBRm | apply:  BRms_nz].
move => [/setC_P [xr  /BRps_iP h] x0]; apply /setC_P; split => // xp.
by case: h.
Qed.

Lemma BR_osr: order_on BR_order BR.
Proof. by have [/opp_osr or <-]:=(sub_osr BR). Qed.

Lemma BR_tor: total_order BR_order.
Proof.
have [or sr]:=BR_osr.
split => // x y; rewrite sr => xr yr.
suff: sub x y \/ sub y x.
  by case => h; [right | left]; apply/opp_gleP; apply/sub_gleP.
case(p_or_not_p (sub x y)) => h; first by left.
have [a ax nay]: exists2 a, inc a x & ~inc a y.
   ex_middle bad; case h => b bx; ex_middle iby; case bad; ex_tac.
right => b iby.
case: (equal_or_not a b) => eab; first by case:nay; rewrite eab.
case: (qleT_ee (BRi_sQ xr ax) (BRi_sQ yr iby)).
  by move => lab; move:(BRi_segment xr ax (conj lab eab)).
move => lab; case: nay; exact: (BRi_segment yr iby (conj lab (nesym eab))).
Qed.

Lemma BR_gleP x y: gle BR_order x y <-> x <=r y.
Proof.
split; first by move/opp_gleP => /sub_gleP [pa pb pc]; split.
by move => [pa pb pc]; apply/opp_gleP /sub_gleP.
Qed.


Lemma rle_cQ x y: ratp x -> ratp y ->
  (x <=q y <-> (BR_of_Q x <=r BR_of_Q y)).
Proof.
move => xsq ysq;split => [lxy | [_ _ se]].
  split; [ by apply: RS_of_Q | by apply: RS_of_Q  | ].
  move => t /Zo_P [ta tb]; apply/Zo_P; split => //; BQo_tac.
case: (qleT_el xsq ysq) => // cxy.
have: inc x (BR_of_Q y) by apply:Zo_i => //; split => //; apply:nesym.
by move/se => /Zo_hi [_].
Qed.

Lemma rlt_cQ x y: ratp x -> ratp y ->
  (x <q y <-> (BR_of_Q x <r BR_of_Q y)).
Proof.
move => xq yq;split; move => [lxy nexy]; split.
+ by apply/(rle_cQ xq yq).
+ move => eq.
  have: inc y (BR_of_Q x) by apply:Zo_i. 
  by rewrite eq; move /Zo_hi => [_].
+ by apply/(rle_cQ xq yq).
+ by dneg xy; rewrite xy.
Qed.

Lemma rleR a: realp a -> a <=r a.
Proof. by move => aQ; split. Qed.

Lemma rleA x y: x <=r y -> y <=r x -> x = y.
Proof. by  move => [_ _ h1] [_ _ h2]; apply: extensionality. Qed.

Lemma rleT y x z:  x <=r y -> y <=r z -> x <=r z.
Proof.
move => [xQ yQ le1] [_ zQ le2]; split => //; apply: (sub_trans le2 le1).
Qed.

Lemma rleNgt a b: a <=r b -> ~(b <r a).
Proof. by move => pa [pb]; case; apply:rleA. Qed.

Lemma rlt_leT b a c: a <r b -> b <=r c -> a <r c.
Proof. 
move => [pa pb] pc;split; first exact: (rleT pa pc).
move => ac; case: pb; apply:rleA => //; ue.
Qed.

Lemma rle_ltT b a c: a <=r b -> b <r c -> a <r c.
Proof. 
move => pa [pb pc];split; first exact: (rleT pa pb).
move => ac; case: pc;apply :rleA => //; ue.
Qed.

Lemma rlt_ltT b a c: a <r b -> b <r c -> a <r c.
Proof. move => pa [pb _]; exact:(rlt_leT pa pb). Qed.


Ltac BRo_tac := match goal with
  | Ha: ?a <=r ?b, Hb: ?b <=r ?c |-  ?a <=r ?c  
     =>  apply: (rleT Ha Hb)
  | Ha: ?a <r  ?b, Hb: ?b <=r ?c |-  ?a <r ?c  
     =>  apply: (rlt_leT Ha Hb)
  | Ha:?a  <=r ?b, Hb: ?b <r ?c |-  ?a <r ?c  
     =>  apply: (rle_ltT Ha Hb)
  | Ha: ?a <r ?b, Hb: ?b <r ?c |-  ?a <r ?c  
     => apply: (rlt_ltT Ha Hb)
  | Ha: ?a <=r ?b, Hb: ?b <r ?a |- _ 
    => case: (rleNgt Ha Hb)
  | Ha: ?x <=r  ?y, Hb: ?y  <=r ?x |- _ 
   => solve [ rewrite (rleA Ha Hb) ; fprops ]
  | Ha: realp ?x  |- ?x <=r ?x  => apply: (rleR Ha)
  | Ha: ?a  <=r  _ |- realp ?a =>  exact (proj31 Ha)
  | Ha:  _ <=r ?a |- realp ?a =>  exact (proj32 Ha)
  | Ha:  ?a <r _ |- realp ?a => exact (proj31_1 Ha) 
  | Ha:  _ <r ?a |- realp ?a => exact (proj32_1 Ha) 
  | Ha: ?a <r ?b  |-  ?a <=r ?b => by move: Ha => []  
end.

Lemma rleT_ee a b:  realp a -> realp b -> a <=r b  \/ b <=r a.
Proof.
move: (proj2 BR_tor); rewrite (proj2 BR_osr) => tor ar br.
by case: (tor _ _ ar br)=> h1; [left | right]; apply /BR_gleP.
Qed.

Lemma rleT_ell a b: realp a -> realp b -> [\/ a = b, a <r b | b <r a].
Proof.
move => ar br; case: (equal_or_not a b); first by constructor 1.
by move => nab; case: (rleT_ee ar br)=> h1; [constructor 2 | constructor 3];
   split => //; apply: nesym.
Qed.

Lemma rleT_el a b: realp a -> realp b -> a <=r b  \/ b <r a.
Proof. 
move=> ar br; case: (rleT_ell ar br).
- by move=> ->; left; BRo_tac.
- by move => [pa _]; left.
- by right.
Qed.

Lemma BR_le_aux1 x a: realp x -> (exists2 b, inc b x & b <q a) ->
    x <r (BR_of_Q a).
Proof.
move => xr [b bx lba]; move:(RS_of_Q (proj32_1 lba)) => sa.
case: (inc_or_not b (BR_of_Q a)); first by move => /Zo_P [_] [h _]; BQo_tac.
move => bna;split; last by move => eq; case: bna; rewrite - eq.
split => // t /Zo_P [ta tb]; apply:(BRi_segment xr bx); BQo_tac.
Qed.

Lemma BR_le_aux2 x a: realp x -> inc a x -> x <r (BR_of_Q a).
Proof.
move => xr ax.
have pf:=(RS_of_Q (BRi_sQ xr ax)).
split; last by  move => eq; move: ax; rewrite eq => /Zo_hi [_]. 
by split => // t /Zo_P [_ tx]; apply: (BRi_segment xr ax tx).
Qed.

Lemma BR_le_aux3 x a: realp x -> ratp a -> ~(inc a x) ->
  (BR_of_Q a) <=r x.
Proof.
move => xr aq h.
have pf:=(RS_of_Q aq).
split => // t tx; move:(BRi_sQ xr tx) => tq;apply: (Zo_i tq).
case: (qleT_ell aq tq) => //.
  by move => eat;case:h; rewrite eat.
move => ta; case: h;exact:(BRi_segment xr tx ta).
Qed.

Lemma BR_le_aux4 x: realp x -> (inc \0q x <-> x <r \0r).
Proof.
move => xr; split => h; first by apply:(BR_le_aux2 xr h). 
ex_middle bad; move:(BR_le_aux3 xr QS0 bad) => h'; BRo_tac.
Qed.

Theorem BR_archimedean  x: realp x -> 
    exists2 n, natp n & x <r (BR_of_Q (BQ_of_nat n)).
Proof.
move => xr.
move/BR_P: (xr) => [pa [y yx] pc pd pe].
have yq := (pa _ yx).
have ha:= (BR_le_aux2 xr yx).
move:(BQ_floorp4 yq) => [n nN le1].
move/(rlt_cQ yq (proj32_1 le1)): le1 => le2.
exists n => //; BRo_tac.
Qed.


Lemma BR_no_greatest x : ~ (greatest BR_order x).
Proof.
move => [xsr xg]. 
rewrite (proj2 BR_osr) in xsr xg.
have [n _ lxn] := (BR_archimedean xsr).
move:(xg _ (proj32_1 lxn)) =>/BR_gleP h; BRo_tac.
Qed.

Lemma BR_no_least x : ~ (least BR_order x).
Proof.
move => [xsr xl].
rewrite (proj2 BR_osr) in xsr xl.
move/BR_P: (xsr) => [pa _ pc pd _].
have [a /setC_P [aq nax]] := (setC_ne (conj pa pc)).
have h1:=(BQsum_Mms aq QmsSm1).
move/(rlt_cQ (proj31_1 h1) (proj32_1 h1)): h1 => h2.
have h3:=(rlt_leT h2 (BR_le_aux3 xsr aq nax)).
move: (xl _ (proj31_1 h3)) => /BR_gleP h4; BRo_tac.
Qed.

Lemma BR_sup_exists X: sub X BR -> nonempty X ->
  bounded_above BR_order X -> has_supremum BR_order X.
Proof.
move => pa pb pc.
have [or sr] :=BR_osr.
move: (pb) => [x0 x0X].
move:(pa _ x0X) => /BR_P [ra rb rc rd re].
have Xsr: sub X (substrate BR_order) by rewrite sr.
move: pc => [z []]; rewrite /upper_bound sr => zr za.
set Y := intersection X.
have YQ: sub Y BQ by move => t ty; exact: (ra _ (setI_hi ty  x0X)).
have zY: sub z Y.
   move => t tx0;apply/setI_P => // i iX.
  by move: (za _ iX) => /BR_gleP [_ _]; apply.
have neY: nonempty Y.
  by move /BR_P: zr => [_ [t tz] _ _ _]; exists t; apply:zY.
have neQ: Y <> BQ.
  move => h; move: (setC_ne (conj ra rc)) => [t /setC_P [ta tb]].
  by move: ta; rewrite - h => ty; move: (setI_hi ty x0X).
have Yr:forall x y, inc x Y -> x <q y -> inc y Y.
   move => x y xY h; apply/(setI_P pb) => i iX.
   move:(pa _ iX) => /BR_P [_ _ _ ra' _]; apply:(ra' _ _  (setI_hi xY iX) h).
case: (p_or_not_p (exists2 w, inc w BQ & Y = Zo BQ (fun z => w <=q z))).
  move => [w wq Yv].
  set Y':= BR_of_Q w.
  have H: realp Y' by apply:RS_of_Q.
  have Ha: sub Y' Y by rewrite Yv => t /Zo_P [tq [ta _]]; apply:Zo_i.
  exists Y';  apply/(lubP or Xsr); rewrite /upper_bound sr; split => //.
    split => // y yX; apply/BR_gleP; split => //; first by apply:pa.
    move => t /Ha ty; exact:(setI_hi ty yX).
  move => Z [Za Zb];apply/BR_gleP; split => // t tz. 
  have: inc t Y. 
     by apply/(setI_P pb) => i iX; move:(Zb _ iX) => /BR_gleP [_ _]; apply.
  case: (equal_or_not w t) => ea; last first.
    by rewrite Yv => /Zo_P [ta tb]; apply:Zo_i.
  move /BR_P: Za => [_ _ _ _ ha]; move:(ha _ tz) => [w']; rewrite - ea.
  move => sa sb sc.
  have: inc w' Y. 
     by apply /(setI_P pb) => i iX; move:(Zb _ iX) => /BR_gleP [_ _]; apply.
   rewrite Yv; move/Zo_hi => sd; BQo_tac.
move => Ha.
have ub: forall x, inc x Y -> exists2 y, inc y Y & y <q x.
  move => a aY;move: (YQ _ aY) => aQ; ex_middle bad.
  have h: forall y, inc y Y -> a <=q y.
    move => y yY; case:(qleT_el aQ (YQ _ yY)) => // ya; case bad; ex_tac.
  case: Ha; exists a => //; set_extens t.
     move/h => aq; apply/Zo_P; split => //; rewrite -/(ratp _); BQo_tac.
  move => /Zo_P [tq aq]; case: (equal_or_not a t) => eq; first by ue.
  apply: (Yr _ _ aY  (conj aq eq)).
have H: realp Y by apply/BR_P. 
exists Y; apply/(lubP or Xsr); rewrite /upper_bound sr; split => //.
  split => // y yX; apply/BR_gleP; split => //; first by apply:pa.
  move => t ty; exact:(setI_hi ty yX).
move => Z [Za Zb];apply/BR_gleP; split => // t tz; apply/(setI_P pb).
by move => i iX; move:(Zb _ iX) => /BR_gleP [_ _]; apply.
Qed.

Lemma BR_inf_exists X: sub X BR -> nonempty X ->
  bounded_below BR_order X -> has_infimum BR_order X.
Proof.
move => pa pb pc.
have [or sr]:= BR_osr.
move: (pb) => [x0 x0X].
have Xsr: sub X (substrate BR_order) by rewrite sr.
set Y := union X.
have YQ: sub Y BQ by move => t /setU_P [u ua /pa h]; apply: (BRi_sQ h ua).
have neY: nonempty Y.
  move:pb=> [z za]; move /BR_P: (pa _ za) => [_ [w wa] _ _ _].
  by exists w; apply/setU_P; exists z.
have YnQ: Y <> BQ.
  move: pc => [z]; rewrite /lower_bound sr; move => [zr za] eYQ.
  move/BR_P: zr => [zq _ h _ _].
  move: (setC_ne (conj zq h)) => [t /setC_P [ta tb]].
  move:ta; rewrite - eYQ => /setU_P [v va /za /BR_gleP [_ _ vb]].
  by case: tb; apply: vb.
have Yc: forall x y, inc x Y -> x <q y -> inc y Y.
  move => x y /setU_P[z za zb] lxy; apply/setU_P; exists z => //.
  move/BR_P: (pa _ zb) => [ _ _ _ h _]; apply: (h _ _ za lxy).
have nlY:forall x, inc x Y -> exists2 y, inc y Y & y <q x.
  move => x  /setU_P[z za zb].
  move/BR_P: (pa _ zb) => [ _ _ _ _ h]; move: (h _ za) => [y ya yb].
  exists y => //; apply/setU_P; ex_tac.
have H: realp Y by apply/BR_P.
exists Y; apply/(glbP or Xsr); rewrite /lower_bound sr; split => //.
  split => // y yX; apply/BR_gleP; split => //; first by apply:pa.
  by move => t ty; apply /setU_P; exists y.
move => Z [Za Zb];apply/BR_gleP; split => // t /setU_P [v va vb].
by move: (Zb _ vb) => /BR_gleP [_ _]; apply.
Qed.

Lemma BRzero_prop: \0r = BQps. 
Proof.
set_extens t; first by move /Zo_P => [_ / qlt0xP].
move => / qlt0xP h; apply:Zo_i => //; exact:(proj32_1 h).
Qed.

Lemma BR_hi_Qps x: inc x BRp -> sub x BQps.
Proof.
move => /Zo_P [h1 h2] t tx.
apply/BQps_iP; split; [by apply: h2 |  move => t0; rewrite t0 in tx].
move/BR_P: h1 => [_ _ _ _ h3]; move:(h3 _ tx) => [y yx / qgt0xP y0].
exact:(BQ_di_neg_pos y0 (h2 _ yx)).
Qed.

Lemma BR_hi_Qps' x: inc x BRps -> ssub x BQps.
Proof. by move/BRps_iP => [/BR_hi_Qps sa]; rewrite BRzero_prop => sb. Qed.

Lemma BRcompare_zero x: inc x BRps -> 
   exists2 y, inc y BQps & BR_of_Q y <r x.
Proof.
move => h.
move:(setC_ne (BR_hi_Qps'  h)) => [y /setC_P [ya yb]].
have h':=(BR_le_aux3 (BRps_sBR h) (BQps_sBQ ya) yb).
case: (equal_or_not (BR_of_Q y) x) => eq; last by ex_tac.
move:(BQhalf_pos ya)(BQhalf_pos1 ya) => sa sb; ex_tac.
by move/(rlt_cQ (proj31_1 sb) (proj32_1 sb)): sb; rewrite eq.
Qed.

Lemma rle0xP x: \0r <=r x <-> inc x BRp.
Proof.
split.
   rewrite BRzero_prop; move => [_ pa pb]; apply:Zo_i => //. 
   apply: (sub_trans pb); apply: BQps_sBQp.
move=> h; split; [apply:RS0 | exact:BRp_sBR | ]. 
rewrite BRzero_prop; exact:(BR_hi_Qps h).
Qed.

Lemma rlt0xP x: \0r <r x <-> inc x BRps.
Proof.
split; first by move => [/rle0xP pa  /nesym pb]; apply /BRps_iP.
by move /BRps_iP => [/rle0xP h /nesym].
Qed.

Lemma rgt0xP x:  x <r \0r <-> inc x BRms.
Proof. 
split; last by move => /setC_P [sa sb]; case: (rleT_el RS0 sa) => // /rle0xP.
move => sa; move:(proj31_1 sa) => xr.
apply/setC_P; split => //; move/rle0xP => h; BRo_tac.
Qed.

Lemma rge0xP x:  x <=r \0r <-> inc x BRm.
Proof. 
case: (equal_or_not x \0r) => xnz.
  rewrite xnz; split => _; [apply:RmS0 | apply: (rleR  RS0)].
split => h; first by move /rgt0xP: (conj h xnz) => /BRms_sBRm.
have /rgt0xP [//]: inc x BRms by apply/BRms_iP. 
Qed.

Lemma rle_par1 x y: inc x BRps -> inc y BRm ->  y <r x.
Proof.  move => /rlt0xP ha /rge0xP hb; BRo_tac. Qed.

Lemma rle_par2 x y: inc x BRp -> inc y BRms ->  y <r x.
Proof.  move => /rle0xP ha /rgt0xP hb; BRo_tac. Qed.

Lemma rle_par3 x y: inc x BRp -> inc y BRm ->  y <=r x.
Proof.  move => /rle0xP ha /rge0xP hb; BRo_tac. Qed.

Lemma RpsS_of_Q x: inc x BQps -> inc (BR_of_Q x) BRps.
Proof. 
move / qlt0xP => h. 
by move/(rlt_cQ (proj31_1 h) (proj32_1 h)):h => /rlt0xP.
Qed.

Lemma RmsS_of_Q x: inc x BQms -> inc (BR_of_Q x) BRms.
Proof. 
move / qgt0xP => h. 
by move/(rlt_cQ (proj31_1 h) (proj32_1 h)):h => /rgt0xP.
Qed.

Lemma RpS_of_Q x: inc x BQp -> inc (BR_of_Q x) BRp.
Proof. 
move / qle0xP => h. 
by move/(rle_cQ (proj31 h) (proj32 h)):h => /rle0xP.
Qed.

Lemma RmS_of_Q x: inc x BQm -> inc (BR_of_Q x) BRm.
Proof. 
move / qge0xP => h. 
by move/(rle_cQ (proj31 h) (proj32 h)):h => /rge0xP.
Qed.

Lemma RpsS1 : inc \1r BRps.
Proof. apply: RpsS_of_Q; apply:QpsS1. Qed.

Lemma RpsS2 : inc \2r BRps.
Proof. apply: RpsS_of_Q; apply:QpsS2. Qed.

Lemma RmsSm1 : inc \1mr BRms.
Proof.  apply: RmsS_of_Q; apply:QmsSm1. Qed.

Lemma RSm1 : realp \1mr.
Proof. apply /BRms_sBR; apply:RmsSm1. Qed.

Lemma RpsSh2 : inc \2hr BRps.
Proof. apply: RpsS_of_Q; apply:QpsSh2. Qed.

Lemma RSh2 : realp \2hr.
Proof. apply /BRps_sBR:RpsSh2. Qed.

Lemma RpsS3 : inc \3r BRps.
Proof. apply: RpsS_of_Q; apply: QpsS3. Qed.

Lemma RS3 : realp \3r.
Proof. exact:(BRps_sBR RpsS3). Qed.

Lemma RpsS4 : inc \4r BRps.
Proof. apply: RpsS_of_Q; apply: QpsS4. Qed.

Lemma RS4 : realp \4r.
Proof. apply /BRps_sBR:RpsS4. Qed.


Lemma infimum_BRp:infimum BR_order BRp = \0r.
Proof.
have [or sr] := BR_osr.
have sr':sub BRp (substrate BR_order) by rewrite sr; apply:BRp_sBR.
symmetry; apply:infimum_pr2 => //;apply/(glbP or) => //; split.
  by hnf; rewrite sr; split;[ apply:RS0 | move => y / rle0xP /BR_gleP].
move => z []; rewrite sr => zr; apply; apply: RpS0.
Qed.


Definition BRopp x := Yo (rationalp x)
   (BR_of_Q (BQopp (BQ_of_R x)))  (fun_image (BQ -s x) BQopp).

Lemma BRopp_Q x: ratp x -> BRopp (BR_of_Q x) = BR_of_Q (BQopp x).
Proof.
move => xq.
by rewrite /BRopp (Y_true (BR_of_Q_prop1 xq)) (BQ_of_R_prop2 xq).
Qed.

Lemma BRopp_irrational x: irrationalp x ->
   BRopp x = (fun_image (BQ -s x) BQopp).
Proof.  by move => xi;rewrite /BRopp Y_false // => [] [sa sb]. Qed.

Lemma RSo x: realp x -> realp (BRopp x).
Proof.
case/BR_rational_dichot => rx.
  move/BR_of_Q_prop2: rx => [y yq ->]. 
  rewrite (BRopp_Q yq);apply:(RS_of_Q (QSo yq)).
rewrite (BRopp_irrational rx); apply /BR_P.
move: rx => [[pa pb pc pd pe] pf].
split.
+ by move => t /funI_P [z /setC_P [za _] ->]; apply: QSo.
+ apply: funI_setne; exact:(setC_ne (conj pa pc)).
+ move => eq; move:(pb) => [y yx].
  move:(QSo (pa _ yx)); rewrite /ratp - eq. 
  move /funI_P => [z /setC_P [za zb] eq2].
  by case: zb; rewrite - (BQopp_inj (pa _ yx) za eq2).
+ move => a b /funI_P [z /setC_P [za zb] ->] h.
  move:(qlt_opp h); rewrite (BQopp_K za) => h1; move: (proj31_1 h1) => xx.
  apply/funI_P; exists (BQopp b). 
    apply/setC_P; split => // h2; case: zb; exact:(pd _ _ h2 h1).
  by rewrite(BQopp_K (proj32_1 h)).
+ move => a /funI_P [z /pf [y /setC_P [ya yb yc]] ->].
  exists (BQopp y); first by apply/funI_P; exists y => //; apply/setC_P.
  apply:(qlt_opp yc).
Qed.

Lemma RSIo x: irrationalp x ->  irrationalp (BRopp x).
Proof.
move => xi.
have ra:=(BRopp_irrational xi).
move: (xi) => [xr pf]; move:(xr) => [pa pb pc pd pe].
split; first by move/BR_P:(xr) => /RSo /BR_P.
move => a /setC_P [aq nax].
have: inc (BQopp a) x. 
  ex_middle h;case: nax; rewrite ra; apply/funI_P; exists (BQopp a).
     by apply/setC_P; split => //; apply:QSo.
  by rewrite (BQopp_K aq).
move/pe => [y yx lya]; move:(qlt_opp lya); rewrite (BQopp_K aq) => la.
exists (BQopp y) => //; apply/setC_P; split;first exact:(proj32_1 la).
rewrite ra; move/funI_P => [z /setC_P[za zb]] /(BQopp_inj (proj31_1 lya) za).
by move => eq; case: zb; rewrite - eq.
Qed.

Lemma BRopp_K x: realp x -> BRopp (BRopp x) = x.
Proof. 
case/BR_rational_dichot => rx.
  move/BR_of_Q_prop2: rx => [y yq ->]. 
  by rewrite (BRopp_Q yq) (BRopp_Q (QSo yq)) (BQopp_K yq).
move:(RSIo rx).
rewrite (BRopp_irrational rx) => h; rewrite (BRopp_irrational h).
set_extens t.
   move => /funI_P [z /setC_P [za zb] ->]; ex_middle k; case: zb.
   have sc:=(QSo za).
   apply/funI_P; exists (BQopp z); [ by apply/setC_P | by rewrite BQopp_K].
move => tx; move:(rx) => [[ha _ _ _ _] _]; move:(ha _ tx) => tq.
apply /funI_P; exists (BQopp t); last by rewrite BQopp_K.
apply/setC_P; split; first by apply:QSo.
move /funI_P => [z /setC_P [za zb]].
by move/(BQopp_inj tq za) => eq;case:zb; rewrite - eq.
Qed.


Lemma BRopp_inj a b: realp a -> realp b -> BRopp a = BRopp b -> a = b.
Proof. 
by move => az bz h;rewrite - (BRopp_K az) h (BRopp_K bz).  
Qed.

Lemma BRopp_fb: bijection (Lf BRopp BR BR).
Proof. 
apply: lf_bijective.
- by move => t /RSo tz.
- apply: BRopp_inj.
- move => y yz; exists (BRopp y); first by apply: RSo. 
  by symmetry;apply BRopp_K.
Qed.

Lemma rle_opp x y: x <=r y ->  (BRopp y) <=r  (BRopp x).
Proof.
move => [xr yr lexy]; split;try apply:RSo => //.
case/BR_rational_dichot:xr => rx; case/BR_rational_dichot:yr => ry.
+ move:lexy;move/BR_of_Q_prop2: rx => [x' x'q ->]. 
  move/BR_of_Q_prop2: ry => [y' y'q ->] H.
  have ha: x' <=q y'. 
     by apply /(rle_cQ x'q y'q); split => //; apply:RS_of_Q.
  move:(qle_opp ha) => /(rle_cQ (QSo y'q) (QSo x'q))  [_ _].
  by rewrite !BRopp_Q.
+ move:lexy;move/BR_of_Q_prop2: rx => [x' x'q ->]; rewrite BRopp_Q //.
  rewrite (BRopp_irrational ry) => lexy.
  move => t /Zo_P [tq ha]; move: (qlt_opp ha); rewrite (BQopp_K x'q) => hb.
  apply/funI_P; exists (BQopp t); last by rewrite (BQopp_K tq).
  apply/setC_P; split; [by apply:QSo | move => ty].
  move:(lexy _ ty) => /Zo_hi [hc _]; BQo_tac.
+ move:lexy;move/BR_of_Q_prop2: ry => [y' y'q ->]; rewrite BRopp_Q //.
  rewrite (BRopp_irrational rx)=> lexy.
  move => t /funI_P [z /setC_P [za zb] ->]; apply:Zo_i;first by apply:QSo.
  case: (qleT_ell y'q za).
  - move => eq; case: zb; rewrite - eq; ex_middle nyx. 
    move:(rx) => [_ irx]. 
    move:(irx _ (setC_i y'q nyx)) => [v /setC_P [va vb] vc].
    by case:vb; apply:lexy; apply/Zo_i.
  - by move => ha; case: zb; apply: lexy; apply /Zo_P.
  - by move/ qlt_opp.
+ rewrite (BRopp_irrational rx) (BRopp_irrational ry).
  move => t /funI_P [z /setC_P[za zb] ->]; apply /funI_P; exists z => //.
  by apply/setC_P; split => //; dneg h; apply: lexy.
Qed.

Lemma rle_oppP x y: realp x -> realp y ->
   ((BRopp y) <=r  (BRopp x) <-> x <=r y).
Proof.
move => xr yr; split; last apply: rle_opp. 
by move => h;move:(rle_opp h); rewrite ! BRopp_K.
Qed.


Lemma rlt_opp x y: x <r y -> (BRopp y) <r (BRopp x).
Proof. 
move => [pa pb]; split; first by apply:rle_opp.
by move: pa => [xz yz _] pc; case: pb; apply:BRopp_inj.
Qed.

Lemma rlt_oppP x y: realp x -> realp y ->
   ((BRopp y) <r  (BRopp x) <-> x <r y).
Proof.
move => xr yr; split; last apply: rlt_opp. 
by move => h;move:(rlt_opp h); rewrite ! BRopp_K.
Qed.

Lemma rle_opp_iso:
  order_isomorphism (Lf BRopp BR BR) BR_order (opp_order BR_order).
Proof. 
move: BR_osr BRopp_fb => [or sr] bf.
have la: lf_axiom BRopp BR BR by move => t tr;apply:RSo.
have [pa pb]:= (opp_osr or).
hnf;rewrite pb; aw;split => //; first by saw.
hnf; aw;move => x y xr yr; rewrite ! LfV//;split.
  by move /BR_gleP => h; apply /opp_gleP; apply /BR_gleP; apply rle_opp.
move /opp_gleP /BR_gleP => h; apply /BR_gleP.
by rewrite - (BRopp_K xr) -(BRopp_K yr); apply rle_opp.
Qed.

Lemma BR_supremum_opp X a (x := supremum BR_order X):
   nonempty X -> (forall t, inc t X -> t <=r a) ->
   x = BRopp (infimum BR_order (fun_image X BRopp)).
Proof.
move => sa sb.
move:BR_osr => [or sr].
have ha': sub  X BR by move => t /sb [].
have asr: inc a (substrate BR_order) by rewrite sr;move: (sa) => [u /sb []].
have ha: sub (fun_image X BRopp) BR. 
  by move => t /funI_P [z /ha' za ->]; apply:RSo.
have hb: nonempty  (fun_image X BRopp) by apply: funI_setne.
have hc':  bounded_above BR_order X by exists a; split => // y /sb /BR_gleP.
have hc: bounded_below BR_order (fun_image X BRopp).
  exists (BRopp a); split; first by move:asr; rewrite sr => /RSo. 
  by move => y /funI_P [t /sb tx ->]; apply/BR_gleP/ rle_opp.
have hd: sub (fun_image X BRopp) (substrate BR_order)  by ue.
have hd': sub X (substrate BR_order) by ue.
move: (infimum_pr or hd (BR_inf_exists ha hb hc)).
move: (supremum_pr or hd' (BR_sup_exists ha' sa hc')). 
rewrite -/x; set y := infimum _ _; move => [[ra1 ra2] rb][[rc1 rc2] rd].
have :  upper_bound BR_order X (BRopp y).
  split; first by move: rc1;rewrite sr => /RSo.
  move => t tx. 
  have: inc (BRopp t) (fun_image X BRopp) by apply/funI_P; ex_tac.
  by move / rc2 /BR_gleP/ rle_opp; rewrite (BRopp_K (ha' _ tx)) => /BR_gleP.
move / rb /BR_gleP => le1.
apply: rleA => //; rewrite - (BRopp_K (proj31 le1)); apply: rle_opp.
have : lower_bound BR_order (fun_image X BRopp) (BRopp x).
   split;first by move: ra1;rewrite sr => /RSo.
   by move => t /funI_P [z / ra2/BR_gleP zX ->]; apply/BR_gleP/ rle_opp.
by move / rd /BR_gleP. 
Qed.



Lemma BRopp_0 : BRopp \0r = \0r.
Proof. by rewrite (BRopp_Q QS0) BQopp_0. Qed.

Lemma BRopp_1 : BRopp \1r = \1mr.
Proof. by rewrite (BRopp_Q QS1) BQopp_1. Qed.

Lemma BRopp_m1 : BRopp \1mr = \1r.
Proof. by rewrite (BRopp_Q QSm1) BQopp_m1. Qed.

Lemma BRopp0_bis x: realp x ->  (x = \0r <-> BRopp x = \0r).
Proof. 
by move:BRopp_0 => o0 /BRopp_K xr; split => h; rewrite ?h ? o0 // - xr h o0.
Qed.

Lemma BRopp_positive1 x: inc x BRps -> inc (BRopp x) BRms.
Proof.
by move /rlt0xP => h;apply/rgt0xP;rewrite - BRopp_0; apply:rlt_opp.
Qed.

Lemma BRopp_positive2 x: inc x BRp -> inc (BRopp x) BRm.
Proof.
by move /rle0xP => h;apply/rge0xP;rewrite - BRopp_0; apply:rle_opp. 
Qed.

Lemma BRopp_negative1 x: inc x BRms -> inc (BRopp x) BRps.
Proof. 
by move /rgt0xP => h;apply/rlt0xP;rewrite - BRopp_0; apply:rlt_opp.
Qed.

Lemma BRopp_negative2 x: inc x BRm -> inc (BRopp x) BRp.
Proof. 
by move /rge0xP => h;apply/rle0xP;rewrite - BRopp_0; apply:rle_opp.
Qed.

(** Addition *)

Definition BRsum x y := 
   union (fun_image x (fun z => (fun_image y (fun t => z +q t)))).

Notation "x +r y" := (BRsum x y) (at level 50).

Lemma BR_sump x y: 
   forall a, inc a (x +r y) <-> 
    exists2 z, inc z x & exists2 t, inc t y & a = z +q t.
Proof.
move => a; split. 
  move /setU_P => [u ua /funI_P [z zx zv]]. 
  move: ua; rewrite zv; move/funI_P => [t ty ->];ex_tac; ex_tac.
move => [z zx [t ty ->]]; apply /setU_P.  
exists (fun_image y [eta BQsum z]); apply/funI_P; ex_tac.
Qed.

Lemma BRsumC x y: x+r y = y +r x.
Proof.
by set_extens a => /BR_sump [z zx [t ty ->]]; 
    apply/BR_sump; ex_tac; ex_tac; rewrite BQsumC.
Qed.

Lemma BRsumA x y z: realp x -> realp y -> realp z ->
  x  +r (y +r z) = (x +r y) +r z.
Proof.
move => /BRi_sQ xr /BRi_sQ yr /BRi_sQ zr.
set_extens t.
  move/BR_sump => [a ax [b /BR_sump [c cy [d dz -> ->]]]].
  rewrite (BQsumA (xr _ ax) (yr _ cy) (zr _ dz)).
  apply/BR_sump; exists (a +q c); first by apply/BR_sump; ex_tac; ex_tac.
  ex_tac.
move/BR_sump => [u /BR_sump [a ax [b iby ->]] [c cz ->]].
rewrite - (BQsumA (xr _ ax) (yr _ iby) (zr _ cz)).
apply/BR_sump; ex_tac;exists (b +q c) => //;apply/BR_sump; ex_tac; ex_tac.
Qed.

Lemma RSs x y: realp x -> realp y -> realp (x +r y).
Proof.
move => /BR_P [pa pb pc pd pe] /BR_P [qa qb qc qd qe]. 
apply/BR_P; split.
+ by move => t/BR_sump [z za [u ua ->]]; apply:QSs; [apply:pa | apply:qa].
+ move:pb qb => [a ax] [b iby]; exists (a +q b); apply/BR_sump.
  ex_tac; ex_tac.
+ move => h. 
  move:(setC_ne (conj pa pc)) => [a /setC_P [aq anx]].   
  move:(setC_ne (conj qa qc)) => [b /setC_P [bq bnx]].   
  move:(QSs aq bq); rewrite /ratp -h; move => /BR_sump [z za [u ua zv]].
  case: (qleT_ell (pa _ za) aq) => l1;first by case: anx; rewrite - l1.    
     by move:(pd _ _ za l1).
  case: (qleT_ell (qa _ ua) bq) => l2;first by case: bnx; rewrite - l2.
     by move:(qd _ _ ua l2).
  by move: (proj2 (BQsum_Mltlt l1 l2)); rewrite zv.
+ move => a b /BR_sump [z za [u ua zv]] l1; apply/BR_sump.
  move:(qa _ ua) (pa _ za)(proj32_1 l1) => uq zq bq.
  have aux: inc (b -q u) x. 
    apply: (pd _ _ za); rewrite -(BQdiff_sum uq zq) BQsumC - zv.
    apply /BQsum_lt2r => //; [ BQo_tac | by apply:QSo].
  by ex_tac; ex_tac; rewrite (BQsum_diff1 uq bq).
+ move =>a /BR_sump [z /pe [b bx bv] [u ua zv]].
  move: (qa _ ua) (pa _ bx)(proj32_1 bv) => uq bq zq.
  have aux: b +q u <q a by rewrite zv; apply/BQsum_lt2r.
  exists (b +q u) => //;apply/BR_sump; ex_tac; ex_tac.
Qed.

Lemma BRsum_AC x y z: realp x -> realp y -> realp z ->
  (x +r y) +r z = (x +r z) +r y.
Proof.
move => xr yr zr.
by rewrite - (BRsumA xr yr zr) - (BRsumA xr zr yr) (BRsumC y).
Qed. 
  
Lemma BRsum_CA x y z: realp x -> realp y -> realp z ->
  x +r (y +r z) = y +r (x +r z).
Proof.
by move => xr yr zr; rewrite  (BRsumA xr yr zr) (BRsumA yr xr zr) (BRsumC x).
Qed.

Lemma BRsum_ACA a b c d: realp a -> realp b -> realp c -> realp d ->
    (a +r b) +r (c +r d) = (a +r c) +r (b +r d).
Proof. 
move => ar br cr dr. 
move: (RSs br dr)(RSs cr dr)=> sa sb.
by rewrite -!BRsumA // (BRsum_CA br cr dr). 
Qed.


Lemma BR_sumQ_aux x y: ratp x -> realp y ->
   (BR_of_Q x) +r y = fun_image y (fun z => x +q z).
Proof.
move => xq /BR_P [qa _ _ qd qe]; set_extens t.
  move => /BR_sump [z /Zo_P [zq xz] [u ub ->]]; apply /funI_P.
  move:(qa _ ub) => uq.
  move/(BQsum_lt2l xq zq uq): xz => xw.
  move/ (BQsum_lt2r (proj31_1 xw) (proj32_1 xw) (QSo xq)): xw.
  rewrite  -/(_ -q _)  (BQdiff_sum1 xq uq)(BQsumC u) => ww.
  have zuq:=(QSs zq uq).
  by exists ((z +q u) -q x); [ apply:(qd _ _ ub) | rewrite BQsum_diff //]. 
move /funI_P => [z / qe [u uy l1] ->]; apply/BR_sump.
move: (proj31_1 l1) (proj32_1 l1) => uq zq.
move/ (BQsum_lt2l uq zq xq):l1 => l2.
move/ (BQsum_lt2r (proj31_1 l2) (proj32_1 l2) (QSo uq)):l2.
rewrite -/( _ -q _) (BQdiff_sum1 uq xq) => l3. 
move:(proj32_1 l3)=> l4.
exists ( (x +q z) -q u); first by apply/Zo_P. 
by ex_tac; rewrite BQsum_diff1 //; apply:QSs.
Qed.


Lemma BR_sumQ_aux1 x y: rationalp x -> irrationalp y ->
  irrationalp (x +r y).
Proof.
move => xra  [/BR_P yr yi]; split.
   apply/BR_P;apply:RSs => //; apply/BR_P; exact: (proj1 xra).
move/BR_of_Q_prop2:xra => [a aq ->].
rewrite (BR_sumQ_aux aq yr) => t /setC_P [tq] /funI_P h.
case: (inc_or_not (t -q a) y) => tay.
   by case:h; ex_tac; rewrite BQsum_diff.
move:(yi _ (setC_i (QS_diff tq aq) tay)) => [b /setC_P [bq bb] bc].
move/(BQsum_lt2l (proj31_1 bc) bq aq): bc; rewrite (BQsum_diff aq tq) => lt.
exists (a+q b) => //; apply /setC_P;split; first by rewrite -/(ratp _);BQo_tac.
move => /funI_P [z zy].
by move/(BQsum_eq2l aq bq (BRi_sQ yr zy)) => bz; case:bb; rewrite bz.
Qed.

Lemma BRsum_cQ x y: ratp x ->  ratp y -> 
  BR_of_Q x +r BR_of_Q y = BR_of_Q (x +q y).
Proof.
move => xq yq.
rewrite (BR_sumQ_aux xq (RS_of_Q yq)).
set_extens t.
   move => /funI_P [z /Zo_P [zq yz] -> ]; apply/Zo_P; split; first by apply:QSs.
   by apply/BQsum_lt2l.
move/Zo_P => [tQ lt]; apply/funI_P; exists (t -q x).
  move/(BQsum_lt2l (proj31_1 lt) tQ (QSo xq)): lt.
  rewrite BQsumC -/(_ -q _) (BQdiff_sum xq yq) (BQsumC _ t)  => lt1.
   apply/Zo_P; split => //; apply: (proj32_1 lt1).
by rewrite BQsum_diff.
Qed.


Lemma BR_plus21: (\2r +r \1r) = \3r.
Proof. by rewrite (BRsum_cQ QS2 QS1) (BQsum_cN NS2 NS1) - (Nsucc_rw NS2). Qed.

Lemma BR_plus31: (\3r +r \1r) = \4r.
Proof. by rewrite (BRsum_cQ QS3 QS1) (BQsum_cN NS3 NS1) - (Nsucc_rw NS3). Qed.

Lemma BRsum_opp_r x: realp x ->  x +r (BRopp x) = \0r.
Proof. 
move => xr.
case/BR_rational_dichot:(xr) => rx.
  move/BR_of_Q_prop2:rx => [a aq ->].
  by rewrite (BRopp_Q aq) (BRsum_cQ aq (QSo aq)) BQsum_opp_r.
rewrite (BRopp_irrational rx).
set_extens t.
   move/BR_sump => [a ax [b /funI_P [c /setC_P [cq ncx] ->] ->]].
   move:(BRi_sQ xr ax) => aq; apply/Zo_P; split; first by apply:QS_diff.
   apply/(qlt_diffP1 cq aq); case:(qleT_ell aq cq) => // sa; case: ncx; try ue.
   exact:(BRi_segment xr ax sa).
move => /Zo_P [tq / qlt0xP tp].
have [a ax h]:=(BRi_lowbound xr tp).
have aq:= (BRi_sQ xr ax).
apply /BR_sump; ex_tac; exists (t -q a); last by rewrite BQsum_diff.
apply /funI_P; exists (a -q t); last by rewrite BQoppB.
by have ha:=(QS_diff aq tq); apply /setC_P; split => //; move/h => [_].
Qed.

Lemma BRsum_opp_l x: realp x -> (BRopp x) +r x = \0r.
Proof. by move => h; rewrite BRsumC BRsum_opp_r. Qed.

Lemma BRsum_0l x: realp x -> \0r +r x  = x.
Proof. 
move => xr.
rewrite (BR_sumQ_aux QS0 xr); set_extens t.
   by move/funI_P  =>[z za ->]; rewrite (BQsum_0l (BRi_sQ xr za)).
by move => tx; apply/funI_P; ex_tac; rewrite (BQsum_0l (BRi_sQ xr tx)).
Qed.

Lemma BRsum_0r x: realp x -> x +r \0r = x.
Proof. by move => xz;rewrite BRsumC BRsum_0l. Qed.

Lemma BRsum_11 : \1r +r \1r = \2r. 
Proof.  by rewrite (BRsum_cQ QS1 QS1) BQsum_11. Qed.

Lemma BRsum_opp_rev a b: realp a -> realp b -> a +r b = \0r ->
   a = BRopp b.
Proof.
move => ar br h.
move: (BRsumA ar br (RSo br)). 
by rewrite (BRsum_opp_r br) h (BRsum_0l (RSo br)) (BRsum_0r ar).
Qed.

Lemma BRoppD x y: realp x -> realp y ->
  BRopp (x +r y) = (BRopp x) +r (BRopp y).
Proof. 
move => xr yr.
move: (RSo xr)(RSo yr) => oxr oyr.
symmetry; apply: BRsum_opp_rev; try apply:RSs => //.
rewrite BRsum_ACA // (BRsumC _ y) (BRsum_opp_r  yr).
by rewrite (BRsumC _ x) (BRsum_opp_r xr)(BRsum_0l RS0).
Qed.

Lemma RpS_sum x y: inc x BRp -> inc y BRp -> inc (x +r y) BRp.
Proof.
move => /Zo_P [pa pb] /Zo_P[pc pd]; apply/Zo_P; split; first by apply: RSs.
move => t /BR_sump [a /pb ax [b /pd bx ->]];apply:(QpS_sum ax bx).
Qed.

Lemma RpsS_sum_r x y: inc x BRp -> inc y BRps -> inc (x +r y) BRps.
Proof. 
move => xp yps; move: (BRps_sBRp yps) => yp.
apply/setC_P; split; first by apply:RpS_sum.
move/set1_P /(BRsum_opp_rev (BRp_sBR xp) (BRp_sBR yp)) => h.
move:(BRopp_positive1 yps); rewrite -h => ha.
exact:(BR_di_neg_pos ha xp).
Qed.

Lemma RpsS_sum_l x y: inc x BRps -> inc y BRp ->  inc (x +r y) BRps.
Proof. by move => pa pb; rewrite BRsumC; apply RpsS_sum_r.  Qed.

Lemma RpsS_sum_rl x y: inc x BRps -> inc y BRps -> inc (x +r y) BRps.
Proof. by move => pa pb; apply: RpsS_sum_r => //; apply:BRps_sBRp.  Qed.

Lemma RmsS_sum_rl x y: inc x BRms -> inc y BRms -> inc (x +r y) BRms.
Proof.
move => xr yr.
move: (BRopp_negative1 xr) (BRopp_negative1 yr) => xr1 yr1.
move: (BRms_sBR xr)(BRms_sBR yr) => xr2 yr2.
move:(RpsS_sum_rl xr1 yr1); rewrite - (BRoppD xr2 yr2) => h.
by move: (BRopp_K (RSs xr2 yr2)) => <-; apply: BRopp_positive1.
Qed.

Lemma RmsS_sum_r x y: inc x BRm -> inc y BRms ->  inc (x +r y) BRms.
Proof. 
move => pa pb.
case: (equal_or_not x \0r) => h; first by rewrite h (BRsum_0l (BRms_sBR pb)).
by apply:RmsS_sum_rl => //; apply/BRms_iP.
Qed.

Lemma RmsS_sum_l x y: inc x BRms -> inc y BRm -> inc (x +r y) BRms.
Proof. by move => pa pb; rewrite BRsumC; apply: RmsS_sum_r. Qed.

Lemma RmS_sum x y: inc x BRm -> inc y BRm -> inc (x +r y) BRm.
Proof.
move => pa pb.
case: (equal_or_not x \0r) => h; first by rewrite h (BRsum_0l (BRm_sBR pb)).
by apply:BRms_sBRm; apply:RmsS_sum_l => //;  apply/BRms_iP.
Qed.


(** ** subtraction *)

Definition BRdiff x y := x +r (BRopp y).

Notation "x -r y" := (BRdiff x y) (at level 50).

Lemma RS_diff x y: realp x -> realp y -> realp (x -r y).
Proof. by move => sa /RSo sb;apply:RSs. Qed.

Lemma BRdiff_diff a b c: realp a -> realp b -> realp c ->
   a -r (b -r c)  = (a -r b) +r c.
Proof.
move => ar br cr; rewrite /BRdiff.
by rewrite (BRoppD br (RSo cr)) (BRopp_K cr) BRsumA //; apply:RSo.
Qed.

Lemma BRdiff_diff2 a b c: realp a -> realp b -> realp c ->
  (a -r b) -r c = a -r (b +r c). 
Proof.
move => ar br cr. 
by rewrite /BRdiff - (BRsumA ar (RSo br) (RSo cr)) BRoppD.
Qed.

Section BQdiffProps5.
Variables (x y z: Set).
Hypotheses (xr: realp x)(yr: realp y)(zr: realp z).

Lemma BRdiff_sum:  (x +r y) -r x = y.
Proof. 
by rewrite /BRdiff BRsumC (BRsumA (RSo xr) xr yr) BRsum_opp_l // BRsum_0l.
Qed.

Lemma BRsum_diff: x +r (y -r x) = y.
Proof. 
by rewrite /BRdiff (BRsumC y) (BRsumA xr (RSo xr) yr) BRsum_opp_r // BRsum_0l.
Qed.

Lemma BRsum_diff1: (y -r x) +r x = y.
Proof. by rewrite (BRsumC) BRsum_diff. Qed.

Lemma BRdiff_sum1:  (y +r x)  -r x = y.
Proof. by rewrite (BRsumC y) BRdiff_sum. Qed.

Lemma BRdiff_xx :  x -r x = \0r.
Proof. exact:BRsum_opp_r.  Qed.

Lemma BRdiff_0r: x -r \0r = x.
Proof. by rewrite /BRdiff BRopp_0 BRsum_0r. Qed.

Lemma BRdiff_0l: \0r -r x = BRopp x.
Proof. by rewrite /BRdiff BRsum_0l //; apply: RSo. Qed.

Lemma BRdiff_sum_simpl_l:  (x +r y) -r  (x +r z) = y -r z.
Proof. by rewrite - (BRdiff_diff2 (RSs xr yr) xr zr) BRdiff_sum. Qed.

Lemma BRdiff_sum_comm: (x +r y) -r z = (x -r z) +r y.
Proof. 
by rewrite /BRdiff (BRsumC x y) (BRsumC _ y) - (BRsumA yr xr) //; apply: RSo. 
Qed.


Lemma BRoppB: BRopp (x -r y) = y -r x.
Proof. by rewrite /BRdiff (BRoppD xr (RSo yr)) (BRopp_K yr) BRsumC. Qed.

End BQdiffProps5.

Section BQdiffProps6.
Variables (x y z: Set).
Hypotheses (xr: realp x)(yr: realp y)(zr: realp z).

Lemma BRsum_diff_ea: x = y +r z -> z = x -r y.
Proof. by move => -> ; rewrite BRdiff_sum. Qed.

Lemma BRdiff_xx_rw:  x -r y = \0r -> x = y.
Proof. 
by move => /(congr1 (BRsum y)); rewrite (BRsum_diff yr xr) BRsum_0r.
Qed.

Lemma BRdiff_sum_simpl_r:  (x +r z) -r (y +r z) = x -r y.
Proof. by rewrite (BRsumC x z) (BRsumC y z);  apply: BRdiff_sum_simpl_l. Qed.

Lemma BRsum_eq2r:  x +r z = y +r z -> x = y.
Proof.
by move => h; rewrite - (BRdiff_sum zr xr) - (BRdiff_sum zr yr) BRsumC h BRsumC.
Qed.

Lemma BRsum_eq2l:  x +r y = x +r z -> y = z.
Proof.
by move => h; rewrite - (BRdiff_sum xr yr) - (BRdiff_sum xr zr) h.
Qed.

End  BQdiffProps6.


Lemma BRdiff_diff_simp a b: realp a -> realp b ->  a -r (a -r b) = b.
Proof.
by move => aq bq; rewrite (BRdiff_diff aq aq bq) (BRdiff_xx aq) BRsum_0l.
Qed.


Lemma BRdiff_cQ x y: ratp x ->  ratp y -> 
  BR_of_Q x -r BR_of_Q y = BR_of_Q (x -q y).
Proof.
move => xr yr.
by rewrite /BRdiff (BRopp_Q yr) (BRsum_cQ xr (QSo yr)).
Qed.

Lemma BRsum_le2r a b c: realp a -> realp b -> realp c ->
    (a +r c <=r b +r c <-> a <=r b).
Proof.
move => ar br cr; split; last first.
  move:(RSs ar cr)(RSs br cr) => Ha Hb.
  move => [_ _ sba]; split  => // t /BR_sump [u ub [v vc ->]].
  apply/BR_sump; exists u; [ by apply:sba | ex_tac ].
move=>[ha hb hc]; split => // t tb.
move /BR_P:(cr) => [pa pb cp pd pe].
move /BR_P:(ar) => [pa' pb' pc' pd' pe'].
move /BR_P:(br) => [pa'' _ _ _ pe''].
move:(pe'' _ tb) => [t' t'b ltt'].
move: (pa'' _ tb)(pa'' _ t'b) => tq t'q.
have dp: inc (t -q t') BQps by apply/ qlt0xP; apply / qlt_diffP1. 
move: (BRi_lowbound cr dp) => [y yc hw]. 
have: (inc (t' +q y) (b +r c)) by apply/BR_sump; ex_tac; ex_tac.
move/hc => /BR_sump [u za [v vc eq]].
have uq: ratp u by apply: pa'.
have vq: ratp v by apply: pa.
have yq: ratp y by apply: pa.
have otq: ratp (BQopp t) by apply: QSo.
have utq :ratp (u +q BQopp t)  by apply:QSs.
have vutq: ratp (v +q (u +q BQopp t)) by apply: QSs.
move: (hw _ vc);rewrite BQdiff_diff // - BQsumA // (BQsumC _ t') BQsumA //.
rewrite (BQsumC y) eq (BQsumC u) - BQsumA //; move / (qgt_diffP vutq vq).
by rewrite BQdiff_sum //; move / (qgt_diffP uq tq); apply: pd'.
Qed.


Lemma BRsum_le2l a b c: realp a -> realp b -> realp c ->
  ((c +r a) <=r (c +r b) <-> a <=r b).
Proof. 
rewrite (BRsumC c) (BRsumC c); apply:BRsum_le2r. 
Qed.


Lemma rle_diffP a b: realp a -> realp b ->  (a <=r b <-> inc (b -r a) BRp).
Proof. 
move => ar br. 
move:(iff_sym (BRsum_le2r ar br (RSo ar))); rewrite (BRsum_opp_r ar) => h.
apply: (iff_trans h); apply/rle0xP.
Qed.

Lemma rle_diffP1 a b: realp a -> realp b -> 
  (a <=r b <-> \0r <=r  (b -r a)).
Proof. 
move => ar br; apply: (iff_trans (rle_diffP ar br)).
apply: iff_sym; exact:rle0xP. 
Qed.

Lemma rlt_diffP a b: realp a -> realp b -> 
  (a <r b <-> inc (b -r a) BRps).
Proof.
move => ar br; split.
  move => [] /(rle_diffP ar br) => pc pd; apply /BRps_iP;split => //.
  dneg aux; symmetry; exact (BRdiff_xx_rw br ar aux).
move /BRps_iP => []  /(rle_diffP ar br) pc pd; split => //.
by dneg aux; rewrite aux (BRdiff_xx br).
Qed.

Lemma rlt_diffP1 a b: realp a -> realp b -> 
  (\0r  <r (b -r a) <-> a <r b).
Proof. 
move => ar br; apply: iff_sym; apply: (iff_trans (rlt_diffP ar br)).
apply:iff_sym ;exact:rlt0xP.
Qed.


Lemma rle_diffP2 a b: realp a -> realp b -> 
  (a <=r b <-> inc (a -r b) BRm).
Proof. 
move => ar br; apply: (iff_trans (rle_diffP ar br)).
rewrite - (BRoppB br ar); split => h; first by apply: BRopp_positive2.
rewrite - (BRopp_K (RS_diff br ar)); apply: (BRopp_negative2 h).
Qed.


Lemma rlt_diffP2 a b: realp a -> realp b -> 
  (a <r b <-> inc (a -r b) BRms).
Proof. 
move => ar br; apply: (iff_trans (rlt_diffP ar br)).
rewrite - (BRoppB br ar); split => h; first by apply: BRopp_positive1.
rewrite - (BRopp_K (RS_diff br ar)); apply: (BRopp_negative1 h).
Qed.


Lemma rgt_diffP  a b: realp a -> realp b -> (a -r b <r \0r <-> a <r b).
Proof.
move => ar br; rewrite - (BRoppB br ar).
apply:iff_sym;apply: (iff_trans(rlt_diffP ar br)); split.
  by move => /BRopp_positive1 / rgt0xP.
by move/ rgt0xP => /BRopp_negative1; rewrite BRopp_K//; apply:RS_diff.
Qed.


Lemma BRsum_lt2l a b c: realp a -> realp b -> realp c -> 
  (c +r a <r c +r b <-> a <r b).
Proof.
move => ar br cr.
apply: (iff_trans (rlt_diffP (RSs cr ar) (RSs cr br))).
apply: iff_sym;apply: (iff_trans (rlt_diffP ar br)).
by rewrite BRdiff_sum_simpl_l.
Qed.

Lemma BRsum_lt2r a b c: realp a -> realp b -> realp c ->
  (a +r c <r b +r c <-> a <r b).
Proof. 
rewrite (BRsumC a c) (BRsumC b c); apply: BRsum_lt2l. 
Qed.

Lemma BRsum_Mlele a b c d: a <=r c ->  b <=r d -> (a +r b) <=r (c +r d).
Proof.
move => eq1 eq2; move: (proj32 eq1) (proj31 eq2)=> cr br.
move/(BRsum_le2r (proj31 eq1) cr br): eq1 => eq3.
move/(BRsum_le2l br (proj32 eq2) cr): eq2 => eq4.
BRo_tac.
Qed.

Lemma BRsum_Mlelt a b c d: a <=r c -> b <r d -> (a +r b) <r (c +r d).
Proof. 
move => eq1 eq2; move: (proj32 eq1)  (proj31_1 eq2)=> cr br.
move /(BRsum_le2r (proj31 eq1) cr br): eq1 => eq3.
move/(BRsum_lt2l br (proj32_1 eq2) cr): eq2 => eq4.
BRo_tac.
Qed.

Lemma BRsum_Mltle a b c d: a <r c -> b <=r d -> (a +r b) <r (c +r d).
Proof.
by move => eq1 eq2; rewrite (BRsumC a)(BRsumC c); apply:BRsum_Mlelt.
Qed.

Lemma BRsum_Mltlt a b c d: a <r c -> b <r d -> (a +r b) <r (c +r d).
Proof. by move => eq1 [eq2 _]; apply: BRsum_Mltle. Qed.


Lemma BRsum_Mlege0 a c d: a <=r c ->  \0r <=r d -> a <=r (c +r d).
Proof.
by move => pa pb; move: (BRsum_Mlele pa pb); rewrite (BRsum_0r (proj31 pa)).
Qed.

Lemma BRsum_Mlegt0 a c d: a <=r c ->  \0r <r d -> a <r (c +r d).
Proof.
by move => pa pb; move: (BRsum_Mlelt pa pb); rewrite (BRsum_0r (proj31 pa)).
Qed.

Lemma BRsum_Mltge0 a c d: a <r c ->  \0r <=r d -> a <r (c +r d).
Proof.
by move => pa pb; move: (BRsum_Mltle pa pb); rewrite (BRsum_0r (proj31_1 pa)).
Qed.

Lemma BRsum_Mltgt0 a c d: a <r c ->  \0r <r d -> a <r (c +r d).
Proof.
by move => pa pb; move: (BRsum_Mltlt pa pb); rewrite (BRsum_0r (proj31_1 pa)).
Qed.

Lemma BRsum_Mlele0 a b c : a <=r c ->  b <=r \0r -> (a +r b) <=r c.
Proof. 
by move => pa pb; move: (BRsum_Mlele pa pb);  rewrite (BRsum_0r (proj32 pa)).
Qed.

Lemma BRsum_Mlelt0 a b c : a <=r c ->  b <r \0r -> (a +r b) <r c.
Proof. 
by move => pa pb; move: (BRsum_Mlelt pa pb);  rewrite (BRsum_0r (proj32 pa)).
Qed.

Lemma BRsum_Mltle0 a b c : a <r c ->  b <=r \0r -> (a +r b) <r c.
Proof. 
by move => pa pb; move: (BRsum_Mltle pa pb); rewrite (BRsum_0r (proj32_1 pa)).
Qed.

Lemma BRsum_Mltlt0 a b c : a <r c ->  b <r \0r -> (a +r b) <r c.
Proof. 
by move => pa pb; move: (BRsum_Mltlt pa pb); rewrite (BRsum_0r (proj32_1 pa)).
Qed.

Lemma BRsum_Mp a b: realp a -> inc b BRp ->  a <=r (a +r b).
Proof. 
move => pa pb.
move/ rle0xP: pb => eq1; exact:(BRsum_Mlege0 (rleR pa) eq1).
Qed.

Lemma BRsum_Mps a b: realp a -> inc b BRps ->  a <r (a +r b).
Proof. 
move => pa pb.
move / rlt0xP: pb => eq1; exact:(BRsum_Mlegt0 (rleR pa) eq1).
Qed.

Lemma BRsum_Mm a b: realp a -> inc b BRm ->  (a +r b) <=r a.
Proof. 
move => pa pb.
by move  / rge0xP: pb => eq1; move:(BRsum_Mlele0 (rleR pa) eq1).
Qed.

Lemma BRsum_Mms a b: realp a -> inc b BRms ->  (a +r b) <r a.
Proof. 
move => pa pb.
by move / rgt0xP: pb => eq1; move:(BRsum_Mlelt0 (rleR pa) eq1).
Qed.

Lemma BRdiff_lt1P a b c: realp a -> realp b -> realp c ->
  (a -r b <r c <-> a -r c <r  b).
Proof.
move => ar br cr.
move: (BRsum_lt2r (RS_diff ar br) cr br).
rewrite (BRsum_diff1 br ar) => ha.
move: (BRsum_lt2r (RS_diff ar cr) br cr).
rewrite (BRsum_diff1 cr ar) BRsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.

Lemma BRdiff_lt2P a b c: realp a -> realp b -> realp c ->
  (c <r a -r b <-> b <r a -r c).
Proof.
move => ar br cr.
move: (BRsum_lt2r cr (RS_diff ar br) br).
rewrite (BRsum_diff1 br ar) => ha.
move: (BRsum_lt2r br (RS_diff ar cr) cr).
rewrite (BRsum_diff1 cr ar) BRsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.


Lemma BRdiff_le2P a b c: realp a -> realp b -> realp c ->
  (c <=r a -r b <-> b <=r a -r c).
Proof.
move => ar br cr.
move: (BRsum_le2r cr (RS_diff ar br) br).
rewrite (BRsum_diff1 br ar) => ha.
move: (BRsum_le2r br (RS_diff ar cr) cr).
rewrite (BRsum_diff1 cr ar) BRsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.


Lemma BRdiff_le1P a b c: realp a -> realp b -> realp c ->
  (a -r b <=r c <-> a -r c <=r  b).
Proof.
move => ar br cr.
move: (BRsum_le2r (RS_diff ar br) cr br).
rewrite (BRsum_diff1 br ar) => ha.
move: (BRsum_le2r (RS_diff ar cr) br cr).
rewrite (BRsum_diff1 cr ar) BRsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.

(** Multiplication *)

Definition BRprod_aux x y := 
   union (fun_image x (fun z => (fun_image y (fun t => z *q t)))).

Definition BRprod x y:=
  Yo (x = \0r) \0r (Yo (inc x BRps)
     (Yo (y = \0r) \0r (Yo (inc y BRps) (BRprod_aux x y) 
            (BRopp (BRprod_aux x (BRopp y)))))
   (Yo (y = \0r) \0r (Yo (inc y BRps) (BRopp (BRprod_aux (BRopp x) y)) 
            (BRprod_aux (BRopp x) (BRopp y))))).

Notation "x *r y" := (BRprod x y) (at level 40).


Fact BR_prod_auxP x y a: 
   inc a (BRprod_aux x y) <-> 
    exists2 z, inc z x & exists2 t, inc t y & a = z *q t.
Proof.
split. 
  move /setU_P => [u ua /funI_P [z zx zv]]. 
  move: ua; rewrite zv; move/funI_P => [t ty ->];ex_tac; ex_tac.
move => [z zx [t ty ->]]; apply /setU_P.  
exists (fun_image y [eta BQprod z]); apply/funI_P; ex_tac.
Qed.

Lemma  BRprod_auxC x y: (BRprod_aux x y) = (BRprod_aux y x). 
Proof.
by set_extens a => /BR_prod_auxP [z zx [t ty ->]]; 
    apply/BR_prod_auxP; ex_tac; ex_tac; rewrite BQprodC.
Qed.

Lemma BRprodC x y:  x *r y = y *r  x.
Proof.
rewrite /BRprod.
case: (equal_or_not x \0r) => ha; first by rewrite !(Y_true ha) !Y_same.
rewrite !(Y_false ha).
case: (equal_or_not y \0r) => hb;first by rewrite !(Y_true hb) !Y_same.
rewrite !(Y_false hb).
rewrite (BRprod_auxC x) (BRprod_auxC _  (BRopp y)) (BRprod_auxC y (BRopp x)).
case: (inc_or_not x BRps) => hc; first by rewrite !(Y_true hc).  
by rewrite !(Y_false hc)  (BRprod_auxC (BRopp y) (BRopp x)).
Qed.

Lemma BRprod_0l x:  \0r *r x = \0r.
Proof. by rewrite /BRprod; Ytac0. Qed.

Lemma BRprod_0r x: x *r \0r = \0r.
Proof. by rewrite BRprodC BRprod_0l. Qed.

Lemma BR_pos_prop x:
   inc x BRps <-> (realp x /\ exists2 y, inc y BQps & ~ inc y x).
Proof.
apply: (iff_trans (iff_sym (rlt0xP x))); split.
  move => [[_ pb pc] pd]; split => //.
  move:(setC_ne (conj pc (nesym pd))) => [y /setC_P [ /Zo_hi/ qlt0xP pa] pe].
  ex_tac.
move => [pa [y / qlt0xP yb yc]]. 
case: (rleT_ell RS0 pa) => // h; case: yc.
  rewrite - h; apply: Zo_i => //. rewrite -/(ratp _);BQo_tac.
move/(BR_le_aux4 pa):h => xp; apply: (BRi_segment pa xp yb).
Qed.

Lemma BR_prod_aux1 x y : inc x BRps -> inc y BRps -> 
  (x *r y) =  (BRprod_aux x y).
Proof.
move => pa pb.
move /BRps_iP:(pa) => [_ xnz].
move /BRps_iP:(pb) => [_ ynz].
by rewrite /BRprod; repeat Ytac0.
Qed.

Lemma RpsS_prod x y : inc x BRps -> inc y BRps -> inc (x *r y) BRps.
Proof.
move => sa sb; rewrite (BR_prod_aux1 sa sb); move: sa sb.
move => /BR_pos_prop [xr [x' x'p x'x]] /BR_pos_prop [yr [y' y'p y'y]].
move: xr yr => /BR_P [pa pb pc pd pe] /BR_P [qa qb qc qd qe]. 
have ha: forall t, inc t x -> x' <q t.
  move => t tx.
  case: (qleT_ell (pa _ tx) (BQps_sBQ x'p)) => lt1 //;  case: x'x; try ue.
  apply: (pd _ _ tx lt1).
have hb: forall t, inc t y -> y' <q t.
  move => t ty.
  case: (qleT_ell (qa _ ty) (BQps_sBQ y'p)) => lt1 //;  case: y'y; try ue.
  apply: (qd _ _ ty lt1).
have hc: exists2 z, inc z BQps & ~ inc z (BRprod_aux x y).
  move: (QpsS_prod x'p y'p) => h; ex_tac => /BR_prod_auxP [u ua [v vb eq]].
  move: (ha _ ua) (hb _ vb) => lt1 lt2.
  move:(proj2(BQprod_Mltltge0 (BQps_sBQp x'p) (BQps_sBQp y'p) lt1 lt2)); ue.
have hb': forall t, inc t y -> inc t BQps.
  move => t /hb l1; apply/ qlt0xP; move / qlt0xP: y'p => l2;BQo_tac. 
apply/BR_pos_prop; split; [apply/BR_P; split | exact].
+ by move => t/BR_prod_auxP [z za [u ua ->]]; apply:QSp;[ apply:pa |apply: qa].
+ move:pb qb => [a ax] [b iby]; exists (a *q b); apply/BR_prod_auxP.
  ex_tac; ex_tac.
+ move => h.
  by move:hc => [z /BQps_sBQ za]; rewrite h; case.
+ move => a b /BR_prod_auxP [z za [u ua zv]] l1; apply/BR_prod_auxP.
  move:(qa _ ua) (pa _ za)(proj32_1 l1) => uq zq bq.
  move: (hb' _ ua) => sa; move: (QpsS_inv sa) => he.
  have unz: u <> \0q by move/BQps_iP: sa => [].
  have aux: inc (b /q u) x.
      apply: (pd _ _ za); rewrite -(BQdiv_prod uq zq unz).
      by apply:(BQprod_Mltgt0 he); rewrite BQprodC - zv.
  by ex_tac; ex_tac; rewrite BQprodC (BQprod_div uq bq unz).
+ move =>a /BR_prod_auxP [z /pe [b bx bv] [u ua zv]].
  move: (qa _ ua) (pa _ bx)(proj32_1 bv) => uq bq zq.
  move:(hb' _ ua) => up.
  have aux: b *q u <q a by rewrite zv; apply:BQprod_Mltgt0.
  exists (b *q u) => //;apply/BR_prod_auxP; ex_tac; ex_tac.
Qed.


Lemma RmsuS_prod x y : inc x BRms -> inc y BRms -> inc (x *r y) BRps.
Proof.
move => sa sb. 
move:(BRopp_negative1 sa)(BRopp_negative1 sb) => sc sd.
rewrite /BRprod (Y_false (BRms_nz sa)) (Y_false (BR_di_neg_spos sa)).
rewrite /BRprod (Y_false (BRms_nz sb)) (Y_false (BR_di_neg_spos sb)).
rewrite - (BR_prod_aux1 sc sd); apply:(RpsS_prod sc sd).
Qed.


Lemma RpmsS_prod x y : inc x BRps -> inc y BRms -> inc (x *r y) BRms.
Proof.
move => sa sb. 
move:(BRopp_negative1 sb) => sd.
rewrite /BRprod (Y_false (BRps_nz sa)) (Y_true sa).
rewrite (Y_false (BRms_nz sb)) (Y_false (BR_di_neg_spos sb)).
rewrite - (BR_prod_aux1 sa sd); move:(RpsS_prod sa sd); apply:BRopp_positive1.
Qed.

Lemma RpS_prod x y: inc x BRp -> inc y BRp -> inc (x *r y) BRp.
Proof.
move => sa sb.
case: (equal_or_not x \0r) => h1; first by rewrite h1 BRprod_0l; apply: RpS0.
case: (equal_or_not y \0r) => h2; first by rewrite h2 BRprod_0r; apply: RpS0.
have xp: inc x BRps by apply/BRps_iP.
have yp: inc y BRps by apply/BRps_iP.
exact:(BRps_sBRp(RpsS_prod  xp yp)).
Qed.


Lemma RmuS_prod x y: inc x BRm -> inc y BRm -> inc (x *r y) BRp.
Proof.
move => sa sb.
case: (equal_or_not x \0r) => h1; first by rewrite h1 BRprod_0l; apply: RpS0.
case: (equal_or_not y \0r) => h2; first by rewrite h2 BRprod_0r; apply: RpS0.
have xp: inc x BRms by apply/BRms_iP.
have yp: inc y BRms by apply/BRms_iP.
exact:(BRps_sBRp (RmsuS_prod  xp yp)).
Qed.


Lemma RpmS_prod x y: inc x BRp -> inc y BRm -> inc (x *r y) BRm.
Proof.
move => sa sb.
case: (equal_or_not x \0r) => h1; first by rewrite h1 BRprod_0l; apply: RmS0.
case: (equal_or_not y \0r) => h2; first by rewrite h2 BRprod_0r; apply: RmS0.
have xp: inc x BRps by apply/BRps_iP.
have yp: inc y BRms by apply/BRms_iP.
exact:(BRms_sBRm (RpmsS_prod  xp yp)).
Qed.

Lemma RSp x y: realp x -> realp y -> realp (x *r y).
Proof.
move => pa pb.
case/BR_i0P:pa => sa;case/BR_i0P:pb => sb.
+ exact:(BRps_sBR(RmsuS_prod sa sb)).
+ rewrite BRprodC; exact (BRm_sBR(RpmS_prod  sb (BRms_sBRm sa))).
+ exact (BRm_sBR((RpmS_prod  sa (BRms_sBRm sb)))).
+ exact:(BRp_sBR(RpS_prod sa sb)).
Qed.


Lemma BRopp_prod_r x y: realp x -> realp y ->
  BRopp (x *r y) = x *r (BRopp y).
Proof.
move => xr yr.
have or :=(BRopp_K yr).
rewrite /BRprod.
have H: y <> \0r -> ~ inc y BRps -> inc (BRopp y) BRps.
  by move => ha hb;  case/(BR_i1P): yr => // /BRopp_negative1.
case: (equal_or_not x \0r) => ha; first by rewrite !(Y_true ha) BRopp_0.
rewrite !(Y_false ha). 
case: (equal_or_not y \0r) => hb.  
  by rewrite !(Y_true hb) hb BRopp_0; Ytac0; Ytac0; rewrite !Y_same BRopp_0.
have hc: (BRopp y <> \0r). 
   by move => h; move:(f_equal BRopp h); rewrite or BRopp_0.
rewrite !(Y_false hb) !(Y_false hc).
case: (inc_or_not x BRps) => hd;[ rewrite !(Y_true hd) | rewrite !(Y_false hd)].
   Ytac he; first by rewrite(Y_false (BR_di_neg_spos (BRopp_positive1 he))) or.
   move:(H hb he) => hf; Ytac0; rewrite - (BR_prod_aux1 hd hf).
   exact:(BRopp_K (BRps_sBR (RpsS_prod hd hf))).
have oxp: inc (BRopp x) BRps by case/(BR_i1P): xr => // /BRopp_negative1.
Ytac he; last by move:(H hb he) => hf; Ytac0.
rewrite(Y_false (BR_di_neg_spos (BRopp_positive1 he))) or.
rewrite - (BR_prod_aux1 oxp he).
exact:(BRopp_K (BRps_sBR (RpsS_prod oxp he))).
Qed.


Lemma BRopp_prod_l x y: realp x -> realp y ->
  BRopp (x *r y) = (BRopp x) *r y.
Proof. by move => xr yr; rewrite BRprodC (BRopp_prod_r yr xr) BRprodC. Qed.

Lemma BRprod_opp_comm x y: realp x -> realp y ->
  x *r  (BRopp y) =  (BRopp x) *r y.
Proof. move => xr yr; rewrite - BRopp_prod_l // BRopp_prod_r //. Qed.

Lemma BRprod_opp_opp x y: realp x -> realp y ->
  (BRopp x) *r (BRopp y) = x  *r y.
Proof. by move => xr yr; rewrite (BRprod_opp_comm (RSo xr) yr) BRopp_K. Qed.

Lemma BR_prodQ_aux x y: inc x BQps -> inc y BRps ->
   (BR_of_Q x) *r y = fun_image y (fun z => x *q z).
Proof.
move => xqps yps. 
have xips:=(RpsS_of_Q xqps).
move/BRps_iP: (xips) => [_ xnz].
move/BRps_iP: (yps) => [_ ynz].
rewrite /BRprod; repeat Ytac0.
move /BR_pos_prop: yps => [/BR_P [qa qb qc qd qe] [y' y'p y'y]].
have hb: forall t, inc t y -> y' <q t.
  move => t ty.
  case: (qleT_ell (qa _ ty) (BQps_sBQ y'p)) => lt1 //;  case: y'y; try ue.
  apply: (qd _ _ ty lt1).
have hb': forall t, inc t y -> inc t BQps.
  move => t /hb l1; apply/ qlt0xP; move / qlt0xP: y'p => l2;BQo_tac.
move/BQps_iP: (xqps) => [ /BQp_sBQ xq xnz'].
set_extens t.
  move => /BR_prod_auxP [z /Zo_P [zq xz] [u ub ->]]; apply /funI_P.
  have uq:= (hb' _ ub).
  move:(BQprod_Mltgt0 (QpsS_inv xqps) (BQprod_Mltgt0 uq xz)). 
  rewrite  -/(BQdiv _ _) (BQdiv_prod xq (BQps_sBQ uq) xnz') => h1.
  have h2:= (qd _ _ ub h1).
  by ex_tac; rewrite BQprod_div //; apply:QSp => //; apply: qa.
move /funI_P => [z / qe [u uy l1] ->]; apply/BR_prod_auxP.
have zq:=(proj32_1 l1).
have up:=(hb' _ uy).
move/BQps_iP: (up) => [ /BQp_sBQ uq unz].
move:(BQprod_Mltgt0 (QpsS_inv up) (BQprod_Mltgt0 xqps l1)). 
rewrite  -/(BQdiv _ _) (BQdiv_prod uq xq unz) => h; move:(proj32_1 h) => h'.
exists ((z *q x) *q BQinv u); first by  apply:Zo_i.
by ex_tac; rewrite BQprodC (BQprodC _ u)  BQprod_div //; apply: QSp.
Qed.

Lemma BRprod_1l x: realp x -> \1r *r x = x.
Proof.
have H: forall x, inc x BRps -> \1r *r x = x.
  move => y yp; move: (BRps_sBR yp) => yq.
  rewrite (BR_prodQ_aux QpsS1 yp); set_extens t.
    by move => /funI_P [z zy ->]; rewrite (BQprod_1l (BRi_sQ yq zy)).
  by move => ty; apply/funI_P; ex_tac; rewrite (BQprod_1l (BRi_sQ yq ty)).
case/BR_i1P; [ by move => ->;rewrite BRprod_0r | by apply: H | ].
move => h; move: (BRopp_negative1 h) => /H.
move: (BRms_sBR h) => xq; move:(RSp RS1 xq) => hq.
by rewrite - (BRopp_prod_r RS1 xq);apply:BRopp_inj.
Qed.

Lemma BRprod_1r x: realp x -> x *r \1r  = x.
Proof. by move => xr; rewrite BRprodC; apply BRprod_1l. Qed.

Lemma BRprod_m1r x: realp x -> x *r \1mr = BRopp x.
Proof. 
by move => xr; rewrite -(BRopp_1) - (BRopp_prod_r xr RS1) (BRprod_1r xr).
Qed.

Lemma BRprod_m1l x: realp x -> \1mr *r x  = BRopp x.
Proof. by  move => xr; rewrite  BRprodC; apply:  BRprod_m1r. Qed.

Lemma BR_prodQ_aux1 x y: x <> \0r -> rationalp x -> irrationalp y ->
  irrationalp (x *r y).
Proof.
move => xnz xra.
wlog: y/ inc y BRps.
  move => H yr; move /BR_P:(proj1 yr) => /BR_i1P; case => ha.
  + by move:(BR_of_Q_prop1 QS0); rewrite -/ BR_zero - ha; move => [_].
  + by apply: H.
  + move:(RSIo (H _  (BRopp_negative1 ha) (RSIo yr))).
    move: (proj1 xra) => /BR_P xr; move: (BRms_sBR ha)=> yr'.
    by rewrite (BRopp_prod_r xr (RSo yr')) BRopp_K. 
move: xnz;move/BR_of_Q_prop2:xra => [a aq ->] anz1 ya yb.
case: (equal_or_not a \0q) => anz; first by case: anz1; rewrite anz.
clear anz1.
have yr:=(BRps_sBR ya).
wlog: a aq anz / inc a BQps.
  move => H; case /BQ_i1P:aq => // ha; first by apply:H => //; apply:BQps_sBQ.
  have hb:= BQopp_negative1 ha.
  have aq:= BQms_sBQ ha.
  have ar:= RS_of_Q aq.
  have hc: BQopp a <> \0q by rewrite -BQopp_0 => /(BQopp_inj aq QS0).
  move:(H _ (BQps_sBQ hb) hc hb).
  rewrite - (BRopp_Q aq) - (BRopp_prod_l ar yr) => /RSIo.
  by rewrite(BRopp_K (RSp ar yr)).
move => ap; split; first by apply/BR_P;apply:(RSp (RS_of_Q aq) yr).
rewrite (BR_prodQ_aux ap ya) => t /setC_P [tq] /funI_P h.
case: (inc_or_not (t /q a) y) => tay.
   by case:h; ex_tac; rewrite BQprod_div.
move:((proj2 yb) _ (setC_i (QS_div tq aq) tay)) => [b /setC_P [bq bb] bc].
move:(BQprod_Mltgt0 ap bc);rewrite BQprodC (BQprod_div aq tq anz) BQprodC => lt.
exists (a *q b) => //; apply /setC_P; split;first by rewrite -/(ratp _);BQo_tac.
move => /funI_P [z zy].
by move/(BQprod_eq2l aq bq (BRi_sQ yr zy)) => bz; case:bb; rewrite bz.
Qed.

Lemma BRprod_cQ x y: ratp x -> ratp y -> 
  BR_of_Q x *r BR_of_Q y = BR_of_Q (x *q y).
Proof.
pose r x y := BR_of_Q x *r BR_of_Q y = BR_of_Q (x *q y).
have H: forall x y, inc x BQps -> inc y BQps -> r x y.
  move => u v up vp.
  rewrite /r (BR_prodQ_aux up (RpsS_of_Q vp)); set_extens t.
    move /funI_P => [z /Zo_P [za zb] ->]; apply/Zo_P; split.
       by apply:QSp => //; apply: BQps_sBQ.
    by rewrite BQprodC (BQprodC u); apply:BQprod_Mltgt0.
  move/BQps_iP: (up) => [ /BQp_sBQ uq unz].
  move/BQps_iP: (vp) => [ /BQp_sBQ vq vnz].
  move => /Zo_P [tq lt]; apply/funI_P.
  move: (BQprod_Mltgt0 (QpsS_inv up) lt). 
  rewrite -/( _/q _)  (BQdiv_prod uq vq unz) => sa; exists (t /q u).
    apply:Zo_i => //; rewrite -/(ratp _);BQo_tac.
  by rewrite (BQprod_div uq tq unz).
have H2: forall x y, inc x BQps -> ratp y -> r x y.
  move => u v up vq;move: (BQps_sBQ up) => uq; case/(BQ_i1P): (vq) => ha.
   + by rewrite /r ha (BQprod_0r uq) -/ BR_zero BRprod_0r.
   + by apply: H.
   + move:(RS_of_Q uq)(RS_of_Q vq) (RS_of_Q (QSp uq vq)) => sa sb sc.
     move:(H u (BQopp v) up (BQopp_negative1 ha)).
     rewrite /r - (BQopp_prod_r uq vq) - (BRopp_Q vq).
     rewrite - (BRopp_Q (QSp uq vq)) - (BRopp_prod_r sa sb).
     by move /(BRopp_inj (RSp sa sb) sc).
case/BQ_i1P => h yq.
+ by rewrite h (BQprod_0l yq) -/ BR_zero BRprod_0l.
+ by apply: H2.
+ move:(BQms_sBQ h) => ha;move:(H2 _ _  (BQopp_negative1 h) (QSo yq)).
  rewrite /r (BQprod_opp_opp ha yq)  - !(BRopp_Q) //.
  by rewrite (BRprod_opp_opp (RS_of_Q ha) (RS_of_Q yq)).
Qed.

Lemma BRprodA x y z: realp x -> realp y -> realp z ->
  x *r (y *r z) = (x *r y) *r z.
Proof.
move: x y z.
pose W x y z := x *r (y *r z) = (x *r y) *r z.
have Ha: forall x y z, inc x BRps -> inc y BRps -> inc z BRps -> W x y z.
  move => x y z xp yp zp.
  rewrite /W (BR_prod_aux1 xp (RpsS_prod yp zp))(BR_prod_aux1 yp zp).
  rewrite  (BR_prod_aux1 (RpsS_prod xp yp) zp) (BR_prod_aux1 xp yp).
  move:(BRi_sQ (BRps_sBR xp))(BRi_sQ (BRps_sBR yp))(BRi_sQ (BRps_sBR zp))
   => ta tb tc.
  set_extens t.
    move/BR_prod_auxP => [a ax [b /BR_prod_auxP [c cy [d dz -> ->]]]].
    rewrite (BQprodA (ta _ ax) (tb _ cy) (tc _ dz)).
    apply/BR_prod_auxP; exists (a *q c); last by ex_tac.
    by apply/BR_prod_auxP; ex_tac; ex_tac.
  move/BR_prod_auxP  => [u /BR_prod_auxP  [a ax [b iby ->]] [c cz ->]].
  rewrite - (BQprodA (ta _ ax) (tb _ iby) (tc _ cz)).
  apply/BR_prod_auxP; ex_tac;exists (b *q c) => //.
  apply/BR_prod_auxP; ex_tac; ex_tac.
have Hb: forall x y z, inc x BRps -> inc y BRps -> realp z -> W x y z.
  move => x y z xp yp /BR_i1P [] zp.
  + by rewrite /W zp !BRprod_0r.
  + by apply: Ha.
  + move:(Ha _ _ _ xp yp (BRopp_negative1 zp)); rewrite /W.
    move: (BRps_sBR xp)(BRps_sBR yp)(BRms_sBR zp) => xr yr zr.
    move:(RSp yr zr) (RSp xr yr) => ha hb.
    by rewrite - !BRopp_prod_r // => /(BRopp_inj (RSp xr ha) (RSp hb zr)).
have Hc: forall x y z, inc x BRps -> realp y -> realp z -> W x y z.
  move => x y z xp  /BR_i1P [] yp zr.
  + by rewrite /W yp !(BRprod_0l,BRprod_0r). 
  + by apply: Hb.
  + move:(Hb _ _ _ xp (BRopp_negative1 yp) zr); rewrite /W.
    move: (BRps_sBR xp)(BRms_sBR yp) => xr yr.
    move:(RSp yr zr) (RSp xr yr) => ha hb.
    rewrite - BRopp_prod_l //  - !BRopp_prod_r // - BRopp_prod_l //. 
    by move => /(BRopp_inj (RSp xr ha) (RSp hb zr)).
move => x y z /BR_i1P [] xp yr zr.
+ by rewrite /W xp ! BRprod_0l. 
+ by apply: Hc.
+ move:(Hc _ _ _ (BRopp_negative1 xp) yr zr); rewrite /W.
  move: (BRms_sBR xp) => xr.
  move:(RSp yr zr) (RSp xr yr) => ha hb.
  by rewrite - !BRopp_prod_l // => /(BRopp_inj (RSp xr ha) (RSp hb zr)).
Qed.

Lemma BRprod_AC x y z: realp x -> realp y -> realp z ->
  (x *r y) *r z = (x *r z) *r y.
Proof.
move => xr yr zr.
by rewrite - (BRprodA xr yr zr) - (BRprodA xr zr yr) (BRprodC y).
Qed.

  
Lemma BRprod_CA x y z: realp x -> realp y -> realp z ->
  x *r (y *r z) = y *r (x *r z).
Proof.
by move => xr yr zr; rewrite (BRprodA xr yr zr) (BRprodA yr xr zr) (BRprodC x).
Qed.

Lemma BRprod_ACA a b c d: realp a -> realp b -> realp c -> realp d ->
    (a *r b) *r (c *r d) = (a *r c) *r (b *r d).
Proof. 
move => ar br cr dr. 
move: (RSp br dr)(RSp cr dr)=> sa sb.
by rewrite -!BRprodA // (BRprod_CA br cr dr). 
Qed.

Lemma BRprodDr x y z: realp x -> realp y -> realp z  ->
   x *r (y +r z) = (x *r y) +r (x *r z).
Proof. 
move: x y z.
pose W x y z := x *r (y +r z) = (x *r y) +r (x *r z).
have HH: forall x, inc x BRps -> sub x BQps.
    move => x /BR_pos_prop [xR [w / qlt0xP wp nnx]] u ux.
    move: (BRi_sQ xR ux) => /BQ_i2P [] // / qge0xP nu.
    case:nnx;apply:(BRi_segment xR ux); BQo_tac.
have Ha: forall x y z, inc x BRps -> inc y BRps -> inc z BRps -> W x y z.
  move => x y z xp yp zp.
  rewrite /W (BR_prod_aux1 xp zp) (BR_prod_aux1 xp yp).
  rewrite (BR_prod_aux1 xp (RpsS_sum_rl yp zp)).
   move:(BRi_sQ (BRps_sBR xp))(BRi_sQ (BRps_sBR yp))(BRi_sQ (BRps_sBR zp))
   => ta tb tc.
  set_extens t.
    move/BR_prod_auxP => [a ax [aa /BR_sump [b iby [c cz ->]]] ->].
    rewrite (BQprodDr (ta _ ax) (tb _ iby) (tc _ cz)).
    apply/BR_sump;exists (a *q b); first by apply/BR_prod_auxP; ex_tac; ex_tac.
    exists (a *q c); [ by apply/BR_prod_auxP; ex_tac; ex_tac | done].
  move => /BR_sump [ab /BR_prod_auxP [a ax [b iby eq1]]].
  move => [ac /BR_prod_auxP [a' a'x [c cz eq2]] ->].
  rewrite eq1 eq2.
  move: (HH _ xp _ ax) (HH _ xp _ a'x) => ap a'p.
  move/BQps_iP: (ap) => [ /BQp_sBQ aq anz].
  move/BQps_iP: (a'p) => [ /BQp_sBQ a'q a'nz].
  move: (tb _ iby) (tc _ cz) => bq cq.
  case: (qleT_el aq a'q) => le1.
    have ha: inc ((c *q a') /q a) z.
      case:(equal_or_not a a') => eq3; first rewrite eq3 BQprodC BQdiv_prod //.
      move:(BQprod_Mltgt0  (HH _ zp _ cz) (conj le1 eq3)) => lt2.
      move:(BQprod_Mltgt0 (QpsS_inv ap) lt2).
      rewrite -/(_ /q _) (BQdiv_prod aq cq anz) (BQprodC a') => lt3.
      by apply:(BRi_segment (BRps_sBR zp) cz).
    have ->: a' *q c = a *q ((c *q a') /q a).
      by rewrite BQprodC BQprod_div => //; apply:QSp.
    rewrite - (BQprodDr aq bq (tc _ ha)).
    apply/BR_prod_auxP; exists a => //; exists (b +q (c *q a') /q a) => //.
    apply /BR_sump; ex_tac;ex_tac.
  have ha: inc ((b *q a) /q a') y.
    move:(BQprod_Mltgt0  (HH _ yp _ iby) le1) => lt2.
    move:(BQprod_Mltgt0 (QpsS_inv a'p) lt2).
    rewrite -/(_ /q _) (BQdiv_prod a'q bq a'nz) (BQprodC a) => lt3.
    by apply:(BRi_segment (BRps_sBR yp) iby).
  have ->: a *q b = a' *q ((b *q a) /q a').
    by rewrite BQprodC BQprod_div => //;apply:QSp.
  rewrite - (BQprodDr a'q (tb _ ha) cq).
  apply/BR_prod_auxP; exists a' => //; exists ((b *q a) /q a' +q c) => //.
  apply /BR_sump; ex_tac;ex_tac.
have Hb: forall x y z, inc x BRps -> inc y BRms -> inc z BRms -> W x y z.
  move => x y z xp yn zn. 
  move:(BRps_sBR xp)(BRms_sBR yn)(BRms_sBR zn) => xr yr zr.
  move: (Ha _ _ _ xp (BRopp_negative1 yn)  (BRopp_negative1 zn)).
  move:(RSs yr zr) (RSp xr yr) (RSp xr zr) => sa sb sc.
  rewrite /W  -(BRoppD yr zr) - ! BRopp_prod_r //  -(BRoppD sb sc).
  by apply:BRopp_inj; [apply:RSp | apply:RSs].
suff Hw :(forall x y z, inc x BRps -> realp y -> inc z BR -> W x y z).
  move => x y z  /BR_i1P [] xn yr zr.
  + by  rewrite xn !BRprod_0l (BRsum_0l RS0).
  + by apply: Hw.
  + move: (BRms_sBR xn) => xr.
    move: (Hw _ _ _ (BRopp_negative1 xn) (RSo yr) (RSo zr)); rewrite /W.
    by rewrite - BRoppD //! BRprod_opp_opp //; apply:RSs.
suff Hv :(forall x y z, inc x BRps -> inc y BRps -> inc z BRms -> W x y z).
  move => x y z xp /BR_i1P []  yr zr.
  + rewrite /W yr BRprod_0r (BRsum_0l zr) BRsum_0l //. 
    by apply: RSp => //; apply:BRps_sBR.
  + case/BR_i1P: zr => w.
    -  rewrite /W w BRprod_0r (BRsum_0r (BRps_sBR yr)) BRsum_0r//.
       by apply: RSp => //; apply:BRps_sBR.
    - by apply:Ha.
    - by apply:Hv.
  +  case/BR_i1P: zr => w.
    - rewrite /W w BRprod_0r (BRsum_0r (BRms_sBR yr)) BRsum_0r //.
      by apply: RSp; [ apply:BRps_sBR |  apply:BRms_sBR].
    - rewrite /W BRsumC (BRsumC (x *r y)); by apply: Hv.
    - by apply: Hb.
move => x y z xp yp zp.
move:(BRps_sBR xp) (BRps_sBR yp) (BRms_sBR zp) => xr yr zr.
have xyr:= RSp xr yr.
have xzr:= RSp xr zr.
have ha: realp (x *r (y +r z)) by apply: RSp => //; apply:RSs.
have hb: realp (x *r (z +r y)) by apply: RSp => //; apply:RSs.
case/BR_i1P: (RSs yr zr) => syz.
+ rewrite /W syz BRprod_0r. 
  move: (BRdiff_xx_rw yr (RSo zr)); rewrite /BRdiff (BRopp_K zr) => h.
  rewrite (h syz) - (BRopp_prod_r xr zr) BRsumC  BRsum_opp_r //.
+ move:(Ha _ _ _ xp syz (BRopp_negative1  zp)).
  rewrite /W -/(_ -r _) BRsumC (BRdiff_sum zr yr) => ->.
  by rewrite - (BRopp_prod_r xr zr) - /(_ -r _) (BRsumC _(x *r z)) BRsum_diff.
+ move:(Hb _ _ _ xp syz (BRopp_positive1 yp)).
  rewrite /W -/( _ -r _) (BRdiff_sum yr zr) => ->.
  rewrite - (BRopp_prod_r xr yr) - /(_ -r _) BRsum_diff //.
Qed.


Lemma BRprodDl x y z: realp x -> realp y -> realp z  ->
   (y +r z) *r x = (y *r x) +r (z *r x).
Proof.
move => xr yr zr; rewrite (BRprodC) (BRprodC y) (BRprodC z).
exact:BRprodDr.
Qed.


Lemma BRprodBr x y z: realp x -> realp y -> realp z  ->
   x *r (y -r z) = (x *r y) -r (x *r z).
Proof. 
by move => xz yz zr; rewrite /BRdiff (BRprodDr xz yz (RSo zr)) BRopp_prod_r. 
Qed.

Lemma BRprodBl x y z: realp x -> realp y -> realp z  ->
  (y -r z) *r x =  (y *r x) -r  (z *r x).
Proof. 
by move => xz yz zr; rewrite BRprodC (BRprodC y) (BRprodC z) BRprodBr.
Qed.


Lemma BRprod_nz x y: realp x -> realp y ->
  x <> \0r -> y <> \0r -> x *r y <> \0r.
Proof. 
move => xr yr  xnz ynz.
case/BR_i1P: xr => //;case/BR_i1P: yr => // sb sa.
+ by move :(RpsS_prod sa sb) => /BRps_iP [].
+ by move :(RpmsS_prod sa sb) => /BRms_iP [].
+ rewrite BRprodC; by move :(RpmsS_prod sb sa) => /BRms_iP [].
+ by move :(RmsuS_prod sa sb) => /BRps_iP [].
Qed.

Lemma BRprod_nz_bis x y: realp x -> realp y ->
  (x *r y = \0r) -> x = \0r \/ y = \0r.
Proof.
move => xr yr pz.
case: (equal_or_not x \0r) => xnz; first by left.
case: (equal_or_not y \0r) => ynz; first by right.
by case: (BRprod_nz xr yr xnz ynz).
Qed.


(* comparison *)

Lemma BRprod_Mlege0 a b c: inc c BRp -> a <=r b -> (a *r c)  <=r (b *r c).
Proof. 
move => cp ab; move: (ab) => [ar br _]; move: (BRp_sBR cp) => cr.
move /(rle_diffP ar br): ab => p1.
apply/ (rle_diffP (RSp ar cr) (RSp br cr)). 
by rewrite - BRprodBl //;apply:RpS_prod.
Qed.


Lemma BRprod_Mltgt0 a b c: inc c BRps -> a <r b -> (a *r c) <r (b *r c).
Proof. 
move => cp ab; move: (ab) => [[ar br _]_]; move: (BRps_sBR cp) => cr.
move /(rlt_diffP ar br): ab => p1.
apply/(rlt_diffP (RSp ar cr) (RSp br cr)).
by rewrite - BRprodBl //;apply:RpsS_prod.
Qed.

Lemma BRprod_Mlele0 a b c: inc c BRm -> a <=r b -> (b *r c)  <=r (a *r c).
Proof. 
move => cm; move: (BRopp_negative2 cm) => ocp ineq. 
move: (BRprod_Mlege0 ocp (rle_opp ineq)).
move: ineq => [ar br _]; move: (BRm_sBR cm) => cr.
rewrite BRprod_opp_opp // BRprod_opp_opp //.
Qed.

Lemma BRprod_Mltlt0 a b c: inc c BRms -> a <r b -> (b *r c) <r (a *r c).
Proof. 
move => cm; move: (BRopp_negative1 cm) => ocp ineq. 
move:  (BRprod_Mltgt0 ocp (rlt_opp ineq)).
move: ineq => [[ar br _] _]; move: (BRms_sBR cm) => cr.
rewrite BRprod_opp_opp // BRprod_opp_opp //.
Qed.

Lemma BRprod_Mpp  b c: inc b BRp -> \1r <=r c -> b <=r (b *r c).
Proof.
move => pa pb.
by rewrite BRprodC - {1} (BRprod_1l (BRp_sBR pa)); apply: BRprod_Mlege0.
Qed.

Lemma BRprod_Mlepp a b c: inc b BRp -> \1r <=r c -> a <=r b -> a <=r (b *r c).
Proof. 
move => pa pb pc; move: (BRprod_Mpp pa pb) => pd; BRo_tac.
Qed.

Lemma BRprod_Mltpp a b c: inc b BRp -> \1r <=r c  -> a <r b -> a <r (b *r c).
Proof. 
move => pa pb pc; move: (BRprod_Mpp  pa pb) => pd;  BRo_tac.
Qed.

Lemma BRprod_Mlelege0 a b c d: inc b BRp -> inc c BRp ->
  a <=r b -> c <=r  d -> (a *r c)  <=r (b *r d).
Proof. 
move => pa pb pc pd.
move: (BRprod_Mlege0 pb pc) (BRprod_Mlege0 pa pd) => r1.
rewrite  (BRprodC c) (BRprodC d) => r2; BRo_tac.
Qed.

Lemma BRprod_Mltltgt0 a b c d: inc b BRps -> inc c BRps ->
  a <r b -> c <r  d -> (a *r c) <r (b *r d).
Proof. 
move => pa pb pc pd.
move: (BRprod_Mltgt0 pb pc) (BRprod_Mltgt0 pa pd) => r1.
rewrite  (BRprodC c) (BRprodC d) => r2; BRo_tac.
Qed.

Lemma BRprod_Mltltge0 a b c d: inc a BRp -> inc c BRp ->
  a <r b -> c <r  d -> (a *r c)  <r (b *r d).
Proof. 
move => pa pb pc pd.
have H: (forall a b, inc a BRp ->  a <r b -> inc b BRps).
   move => u v / rle0xP sa sb; apply/ rlt0xP; BRo_tac.
move: (H _ _ pa pc) (H _ _ pb pd) => bp cp.
case: (equal_or_not c \0r) => cnz.
  by rewrite cnz BRprod_0r;  apply / rlt0xP; apply: RpsS_prod.
by apply: BRprod_Mltltgt0 => //; apply/ BRps_iP;split.
Qed.

Lemma BRprod_ple2r a b c: realp a -> realp b -> inc c BRps ->
  ((a *r c)  <=r (b *r c) <-> a <=r b).
Proof.
move => pa pb pc; split; last by apply:BRprod_Mlege0; exact:(BRps_sBRp pc).
move => h; case: (rleT_el pa pb) => // h1.
move: (BRprod_Mltgt0 pc h1) => h2; BRo_tac.
Qed.


Lemma BRprod_Mgt0le a b c: realp a -> realp b -> inc c BRps ->
  ((c *r a)  <=r (c *r b) <-> a <=r b).
Proof.
by move => pa pb pc; rewrite (BRprodC c) (BRprodC c); apply: BRprod_ple2r.
Qed.


Lemma BRprod_plt2r a b c: realp a -> realp b ->  inc c BRps ->
  ((a *r c) <r (b *r c) <-> a <r b).
Proof.
move => pa pb pc; split; last by apply:BRprod_Mltgt0. 
move => h; case: (rleT_el pb pa) => //.
move /(BRprod_ple2r pb pa pc) => h2; BRo_tac.
Qed.


Lemma BRprod_mle2r a b c: realp a -> realp b -> inc c BRms ->
  ((b *r c)  <=r (a *r c) <-> a <=r b).
Proof.
move => pa pb pc; split; last by apply:BRprod_Mlele0; exact:(BRms_sBRm pc).
move => h; case: (rleT_el pa pb) => // h1.
move: (BRprod_Mltlt0 pc h1) => h2; BRo_tac.
Qed.

Lemma BRprod_mlt2r a b c: realp a -> realp b ->  inc c BRms ->
  ((b *r c)  <r (a *r c) <-> a <r b).
Proof.
move => pa pb pc; split; last by apply:BRprod_Mltlt0.
move => h; case: (rleT_el pb pa) => //.
move /(BRprod_mle2r pb pa pc) => h2; BRo_tac.
Qed.


Definition BRsquare x := x *r x.

Lemma RpS_square x: realp x -> inc (BRsquare x) BRp.
Proof.
case/BR_i0P => h; first exact:(BRps_sBRp (RmsuS_prod h h)).
exact: (RpS_prod h h).
Qed.

Lemma BRsqrt2_prop: inc BRsqrt2 BRps /\ BRsquare  BRsqrt2 = \2r.
Proof.
move: (proj1 sqrt2_irrational) => /BR_P xr.
have sp: inc BRsqrt2 BRps.
  have ha: ~ inc \1q BRsqrt2.
    move /Zo_hi; rewrite (BQprod_1r QS1); move: qlt_12 => ha [hb _]; BQo_tac.
  have hb:=(BR_le_aux3 xr QS1 ha).
  have hc: \0r <r \1r by apply/ rlt0xP; apply:RpsS1.
  apply/rlt0xP;BRo_tac. 
split => //; rewrite /BRsquare (BR_prod_aux1 sp sp);set_extens t.
  move:(BQps_sBQp QpsS2) => hw.
  move/BR_prod_auxP => [a /Zo_P[ap ha] [b /Zo_P[bp hb] ->]]; apply/Zo_P.
  have abp:= (QpsS_prod ap bp).
  split ; [ exact:BQps_sBQ | case:(qleT_el  (BQps_sBQ abp)QS2) => // h].
  move:(BQprod_Mlelege0 hw (BQps_sBQp abp) h h) => h1.
  move: (BQps_sBQ ap)(BQps_sBQ bp) => aq bq.
  move:(BQprod_Mltltge0 hw hw ha hb);rewrite BQprod_ACA // => h2; BQo_tac.
move => /Zo_P [ta tb]; apply /BR_prod_auxP.
move/BQ_P:(ta) => [_ ha hb _].
move: (BQdiv_numden ta) (BQ_of_Z_iQps  hb) (BQ_of_Z_iQ ha).
set a := BQ_of_Z (P t); set b := BQ_of_Z (Q t) => pa bp aq.
rewrite -pa in tb |- *.
move/BQps_iP: (bp) => [/BQp_sBQ bq bnz].
move:(BQprod_Mltgt0 bp tb); rewrite (BQprodC (a /q b)) (BQprod_div bq aq bnz).
move => ga2b. 
have a2q:= QSp QS2 aq.
have hc := BZps_sBZ hb.
have ap: inc a BQps.
  move:(QpsS_prod QpsS2 bp) => / qlt0xP h1; apply/ qlt0xP; BQo_tac.
set d := \2q *q a +q \1q.
set dd:= (\2q *q a) *q (\2q *q a).
have deq: BQsquare d  = (dd  +q \1q) +q \4q *q a.
  rewrite (BQsum_square a2q QS1) /BQsquare  (BQprod_1r a2q) (BQprod_1r QS1).
  by rewrite -/dd /BQdouble (BQprodA QS2 QS2 aq) BQprod_22.
have lt1: \2q *q a *q d +q \1q <q BQsquare d. 
  have ddq: ratp dd by apply:QSp.
  rewrite deq /d (BQprodDr a2q a2q QS1) -/dd (BQprod_1r a2q).
  rewrite - (BQsumA ddq a2q QS1) (BQsumC _ \1q) (BQsumA ddq QS1 a2q).
  have sa:=(BQprod_Mltgt0  ap qlt_24).
  by apply/(BQsum_lt2l (proj31_1 sa) (proj32_1 sa) (QSs ddq QS1)).
have lt2: \1q <=q (a -q \2q *q b) *q b.
  have te :=(ZSp ZS2 hc).
  have tc:= ZSo te.
  have td:intp (P t +z BZopp (\2z *z Q t)) by apply:ZSs.
  rewrite (BQprod_cZ ZS2 hc) /BQdiff BQopp_cZ.
  rewrite (BQsum_cZ ha tc); rewrite (BQprod_cZ td hc).
  apply/ (qle_cZ ZS1 (ZSp td hc)); apply:BZ1_small.
  apply:ZpsS_prod => //; apply/zlt_diffP => //.
  move: (ga2b);rewrite (BQprod_cZ ZS2 hc). 
  by move/(qlt_cZ (ZSp ZS2 hc) ha) => hd.
have lt3: \2q *q BQsquare (b *q d) <q
   (a *q b) *q BQsquare d -q ((\2q *q a) *q d +q \1q).
  have dq:  ratp d by exact:(QSs a2q QS1).
  have d2pq:= (BQpS_square dq); have d2q := (BQp_sBQ d2pq).
  have a2bq:=QS_diff aq (QSp QS2 bq).
  have bddq := QSp bq d2q.
  move:(BQprod_Mlege0 d2pq lt2); rewrite (BQprod_1l d2q) => lt3.
  move:(qlt_leT lt1 lt3); rewrite - (BQprodA a2bq bq d2q).
  rewrite (BQprodBl bddq aq (QSp QS2 bq)) (BQprodA aq bq d2q).
  rewrite - (BQprodA QS2 bq bddq) (BQprodA bq bq d2q).
  rewrite {2}/BQsquare (BQprod_ACA bq bq dq dq) -/(BQsquare _) => l2.
  have uq:= (QSs (QSp (QSp QS2 aq) dq) QS1).
  have vq := QSp (QSp aq bq) d2q.
  have wq := QSp QS2 (BQp_sBQ (BQpS_square (QSp bq dq))).
  move/(BQsum_lt2l uq (proj32_1 l2) wq): l2; rewrite (BQsum_diff wq vq) => l3.
  move: (proj2 (BQsum_lt2r  (proj31_1 l3) vq (QSo uq)) l3).
  by move:(BQdiff_sum uq wq); rewrite BQsumC /BQdiff => hh; rewrite {1} hh.
have dp: inc d BQps by exact: (QpsS_sum_rl (QpsS_prod QpsS2 ap) QpsS1).
have lt5: \1q <=q (a *q b) *q (d *q d).
  have ra:= (BQps_sBQp(QpsS_prod QpsS2 ap)).
  have aap: inc (P t) BZps. 
      move/BZ_i2P: ha; case =>// /BQ_of_Z_iQm hf; case:(BQ_di_pos_neg ap hf).
  have d2: \1q <=q (a *q b).
     rewrite (BQprod_cZ ha hc); apply/ (qle_cZ ZS1 (ZSp ha hc)).
     by apply:BZ1_small; apply:ZpsS_prod. 
  have d1: \1q <=q d by rewrite /d BQsumC; apply: (BQsum_Mp QS1).
  apply:( BQprod_Mpp1 d2 (BQprod_Mpp1 d1 d1)).
have lt4: \0q <q (a *q b) *q (d *q d).
  apply / qlt0xP; exact: (QpsS_prod (QpsS_prod ap bp) (QpsS_prod dp dp)).
pose prop m := (a *q b) *q BQsquare d <q BQsquare (BQ_of_nat m).
move:(BQ_floorp4 (proj32_1 lt4)) => [n0 n0N n0a].
have prop3: prop n0.
  rewrite /prop;move:(BQ_nat_square_monotone n0N)  => he; BQo_tac.
case: (least_int_prop2 n0N prop3).
  rewrite /prop /BQsquare (BQprod_0r QS0); move => [hhh _]; BQo_tac.
set m := cpred _;move => [mN ma npm].
case: (equal_or_not m \0c) => mz.
  move: ma; rewrite /prop mz succ_zero /BQsquare (BQprod_1r QS1) => hf; BQo_tac.
set c := (BQ_of_nat m).
have cp:inc c BQps.
  apply :BQ_of_Z_iQps; apply/BZps_iP; split; first by apply:BZ_of_natp_i.
  by move/BZ_of_nat_inj.
move: (BQps_sBQ  cp) (BQps_sBQ dp) => cq dq.
case: (qleT_el (QSp cq cq) (proj31_1 ma)) => // hf. 
have lt6:  c /q (b *q d) <=q (a*q d) /q c.
  apply/ (BQdiv_Mlelege0 cq (QpsS_prod bp dp) (QSp aq dq) cp).
  by rewrite (BQprod_ACA bq dq aq dq) (BQprodC b).
case: (qleT_el cq (QSp aq dq)) => lt7; last first.
  move:(BQprod_Mltltgt0 cp (QpsS_prod ap dp) lt7 lt7).
  rewrite (BQprod_ACA aq dq aq dq) => lt8.
  move: (qlt_leT lt8 hf).
  move/(BQprod_plt2r (QSp aq aq) (QSp aq bq) (QpsS_prod dp dp)).
  rewrite (BQprodC _ b); move/(BQprod_plt2r aq bq ap) => lab.
  suff H: b <=q \2q *q b by case:(qleNgt (qleT (proj1 lab) H) ga2b).
  rewrite BQprodC; apply:(BQprod_Mpp (BQps_sBQp bp) (proj1 qlt_12)).
have lt8: (\1q +q \2q *q c) <=q ((\2q *q a) *q d +q \1q).
   move: (BQprod_Mlege0 (BQps_sBQp QpsS2) lt7).
   rewrite BQprodC (BQprodC _ \2q) (BQprodA QS2 aq dq) (BQsumC _ \1q)=> h.
   exact:(proj2 (BQsum_le2l (proj31 h)(proj32 h) QS1) h).
move: ma; rewrite /prop /BQ_of_nat (Nsucc_rw mN) - (BZsum_cN mN NS1).
rewrite - (BQsum_cZ (BZ_of_nat_i mN) ZS1) -/(BQ_of_nat _) -/c -/BQ_one.
rewrite (BQsum_square cq QS1)  /BQsquare (BQprod_1r cq) (BQprod_1r QS1). 
rewrite - (BQsumA (QSp cq cq) QS1 (QSp QS2 cq)) => lt9.
move/(qle_oppP (proj31 lt8)(proj32 lt8)): lt8 => le88.
move:(BQsum_Mltle lt9 le88). 
set X := ( X in _ <q X ).
have ->: X = c *q c.
  by rewrite /X -/(_ -q _) (BQdiff_sum1 (QSs QS1 (QSp QS2 cq)) (QSp cq cq)).
move => lt10; move: (qlt_leT lt3 (proj1 lt10)) => lt11.
set u :=  c /q (b *q d).
move: (QpsS_prod bp dp) => sa;move: (QpsS_prod sa sa) => sb.
have u2: inc u BRsqrt2. 
  apply/Zo_P; split; first apply:(QpsS_div cp sa).
  move/ (BQprod_Mltgt0 (QpsS_inv sb)): lt11.
  move/BQps_iP: (sb) => [ /BQp_sBQ sc qdnz].
  rewrite (BQprodC \2q) -/(_ /q _) (BQdiv_prod sc QS2 qdnz).
  have -> //:(c *q c) *q BQinv ((b *q d) *q (b *q d)) = u *q u.
  move: (QSp bq dq) => se; move:(QS_inv se) => sf.
  by rewrite (BQprod_inv se se) (BQprod_ACA cq cq sf sf). 
set v := (a *q d) /q c.
have v2 : inc v BRsqrt2.
  case: (equal_or_not u v) => cuv; first by rewrite - cuv; exact u2.
  move: (sqrt2_irrational) => [[_ _ _ h _] _]; exact:(h _ _ u2 (conj lt6 cuv)).
exists u; [exact | exists v; [ exact |]].
have sf:=(QS_div aq bq).
move/BQps_iP: (dp) => [_ dnz].
move/BQps_iP: (cp) => [_ cnz].
rewrite /u/v /BQdiv (BQprodC _  (BQinv c)).
rewrite (BQprod_ACA cq (QS_inv (QSp bq dq)) (QS_inv cq)(QSp aq dq)).
rewrite (BQprodC (BQinv (b *q d))) (BQprod_inv bq dq).
rewrite (BQprod_ACA aq dq (QS_inv bq) (QS_inv dq)).
rewrite (BQprod_inv1 dq dnz).
by rewrite (BQprod_1r sf) (BQprod_inv1 cq cnz) (BQprod_1l sf). 
Qed.

Lemma BRsquare_mon1 x y: 
  inc x BRp -> inc y BRp -> x <=r y -> BRsquare x <=r BRsquare y.
Proof. move => ha hb hc; exact: (BRprod_Mlelege0 hb ha hc hc). Qed.

Lemma BRsquare_mon2 x y:
  inc x BRp -> inc y BRp -> BRsquare x <=r BRsquare y -> x <=r y.
Proof.
move => ha hb hc; case: (rleT_el (BRp_sBR ha)(BRp_sBR hb)) => // hd.
move: (BRprod_Mltltge0 hb hb hd hd) => he; BRo_tac.
Qed.

Lemma BRsqrt_unique x: inc x BRp ->
  singl_val2 (inc^~ BRp) (fun z => x = BRsquare z).
Proof.
move => xp u v /= ur up vr vp.
have ha: BRsquare v <=r BRsquare v by rewrite - vp;apply:(rleR (BRp_sBR xp)).
by rewrite up in vp; apply: rleA; apply:BRsquare_mon2 => //; rewrite vp.
Qed.


(** Inverse *)


Definition BRinv x (aux:= fun z => BQps -s fun_image z BQinv) :=
   Yo (rationalp x)
   (BR_of_Q (BQinv (BQ_of_R x)))
    (Yo (inc x BRps) (aux x) (BRopp (aux (BRopp x)))).


Lemma BRinv_Q x: ratp x -> BRinv (BR_of_Q x) = BR_of_Q (BQinv x).
Proof.
by move => xq; rewrite /BRinv (Y_true (BR_of_Q_prop1 xq))(BQ_of_R_prop2 xq).
Qed.

Lemma BRinv_0: BRinv \0r = \0r.
Proof. by rewrite (BRinv_Q QS0) BQinv_0. Qed.

Lemma BRinv_irrational x (aux:= fun z => BQps -s fun_image z BQinv):
   irrationalp x ->
   BRinv x = (Yo (inc x BRps) (aux x) (BRopp (aux (BRopp x)))).
Proof.
by move => xi; rewrite /BRinv Y_false // => [] [sa sb]. Qed.

Lemma RpsS_inv x: inc x BRps -> inc (BRinv x) BRps.
Proof.
move => xp.
case/BR_rational_dichot: (BRps_sBR xp) => rx.
  move: xp;move/BR_of_Q_prop2: rx => [y yq ->] h. 
  rewrite (BRinv_Q yq); apply:RpsS_of_Q; apply: QpsS_inv.
  case/BQ_i2P: yq => // /RmS_of_Q hh; case: (BR_di_pos_neg h hh).
rewrite (BRinv_irrational rx) (Y_true xp).
set Y := (BQps -s fun_image x BQinv).
move: rx => [[pa pb pc pd pe] pf].
move: (BR_hi_Qps' xp) => pa''.
have yp1: forall y, inc y (BQps -s x) -> inc (BQinv y) Y.
  move => y /setC_P [yp ynx];  apply/Zo_P; split; first apply:(QpsS_inv yp).
  move /funI_P => [z za zb]; move:(BQinv_inj (BQps_sBQ yp)(pa _ za) zb) => h.
  by case: ynx; rewrite h.
have yp2: forall y, inc y x -> inc (BQinv y) (BQps -s Y).
  move => y yx; apply/Zo_P; split;first exact:(QpsS_inv ((proj1 pa'') _ yx)).
  move /Zo_hi /funI_P ; case; ex_tac.
have Yp: sub Y BQp by apply: sub_trans (BQps_sBQp); apply: Zo_S.
apply/BRps_iP; split; last first.
  move: pb => [u0 /yp2 u0x] eq; move: u0x. 
  rewrite eq - BRzero_prop setC_v; case; case.
apply:Zo_i; [apply/BR_P; split | exact: Yp].
+ apply:(sub_trans Yp BQp_sBQ).
+ move:(setC_ne pa'') => [u /yp1 yy]; ex_tac.
+  move => hc;rewrite hc in Yp. 
   by move:(BQ_di_neg_pos QmsSm1); apply; apply: Yp QSm1.
+ move => a b /setC_P [ap  aby] lab. 
  have bp: inc b BQps by move/ qlt0xP: ap => ap; apply/ qlt0xP; BQo_tac.
  apply/setC_P;split => //.
  move:(BQinv_K (BQps_sBQ ap)) => eq1.
  move => /funI_P [c cx bv]; case: aby; apply /funI_P; exists (BQinv a) => //.
  apply:(pd _ _ cx). 
  move /(BQprod_Mlt1 (BQps_sBQ ap) bp): lab. 
  rewrite bv /BQdiv (BQinv_K (pa _ cx))  BQprodC => H.
  by apply/(BQprod_Mlt1 (pa _ cx) (QpsS_inv ap)); rewrite /BQdiv eq1.
+ move => y /Zo_P [ya yb]; move: (BQps_sBQ ya) => yq.
  move: (QpsS_inv ya)(BQinv_K yq) => yc yd.
  have /pf [z /setC_P[za zb] zc]: inc (BQinv y) (BQ -s x). 
    by  apply/setC_P; split; [ apply:QS_inv | dneg w; apply/funI_P; ex_tac].
  have zp:inc z BQps by move/ qlt0xP: yc => yc; apply/ qlt0xP;BQo_tac.
  exists (BQinv z); first by apply: yp1; apply/setC_P. 
  move:(BQps_nz ya)(BQps_nz zp) => ynz znz.
  move:(BQprod_Mltgt0 (QpsS_inv zp)(BQprod_Mltgt0 ya zc)).
  rewrite BQprodC (BQprodC _ y) (BQprod_inv1 yq ynz) (BQprod_1r (QS_inv za)).
  by rewrite -/((z *q y) /q z) (BQdiv_prod za (BQps_sBQ ya) znz).
Qed.

Lemma BRinv_opp x: realp x -> BRinv (BRopp x) = BRopp (BRinv x).
Proof. 
move => xr.
case/BR_rational_dichot: (xr) => rx.
  move/BR_of_Q_prop2: rx => [y yq ->]. 
  move:(QSo yq) (QS_inv yq) => oyq iyq.
  rewrite (BRinv_Q yq) (BRopp_Q yq)(BRinv_Q oyq).
  by rewrite (BRopp_Q iyq) (BQinv_opp yq).
rewrite (BRinv_irrational rx) (BRinv_irrational (RSIo rx)).
case/BR_i2P: (xr) => h.
  move:(BRopp_positive1 h) => h2.
  by rewrite (Y_false (BR_di_neg_spos h2)) (Y_true h)(BRopp_K xr).
case:(inc_or_not x BRps) => h1; first case:(BR_di_pos_neg h1 h).
have xn:inc x BRms. 
  apply/BRms_iP; split => // xe; case:(proj2(BR_of_Q_prop1 QS0)).
  by rewrite -/BR_zero - xe.
move:(BRopp_negative1 xn) => h2.
move:(BRps_sBR(RpsS_inv h2)); rewrite (BRinv_irrational (RSIo rx)).
by rewrite (Y_true h2) (Y_false h1); move /BRopp_K => ->.
Qed.

Lemma RmsS_inv x: inc x BRms -> inc (BRinv x) BRms.
Proof.
move => h;move:(BRms_sBR h) => h'.
rewrite - (BRopp_K h') (BRinv_opp (RSo h')); apply:BRopp_positive1.
exact:(RpsS_inv (BRopp_negative1 h)).
Qed.

Lemma RS_inv x: realp x -> realp (BRinv x).
Proof.
case /BR_i1P => xs.
+ rewrite xs BRinv_0; apply:RS0.
+ exact: (BRps_sBR (RpsS_inv xs)).
+ exact: (BRms_sBR(RmsS_inv xs)).
Qed.

Lemma RIS_inv x: irrationalp x -> irrationalp (BRinv x).
Proof.
wlog xp: x/ inc x BRps.
  move => H xr.
  move /BR_P: (proj1 xr) => /BR_i1P; case => sx.
  + by case:(proj2(BR_of_Q_prop1 QS0)); rewrite -/BR_zero - sx.
  + by apply:H.
  + move: (H _ (BRopp_negative1 sx) (RSIo xr)). 
    rewrite (BRinv_opp (BRms_sBR sx)) => /RSIo.
    by rewrite (BRopp_K (RS_inv (BRms_sBR sx))).
move => xi.
move:(RS_inv (BRps_sBR xp)) => /BR_P.
rewrite (BRinv_irrational xi) (Y_true xp) => sa.
split => // t /setC_P [tq h].
move:(xi) => [[pa pb pc pd pe] pf].
move: (BR_hi_Qps' xp) => [pa' _].
case/BQ_i2P: tq => tp; last first.
  move: pb => [u ux]; move:(pa' _ ux) => up; move:(QpsS_inv up) => iup.
  exists (BQinv u).
    apply/setC_P; split; first by apply:BQps_sBQ.
    move /setC_P => [_] []; apply/funI_P; ex_tac.
  move/ qge0xP: tp => sc; move/ qlt0xP: iup => sd; BQo_tac.
have /funI_P[u ux ->]:inc t (fun_image x BQinv).
   ex_middle bad; case:h; apply/setC_P; split => //.
move:(pe _ ux) => [v vx lt1];exists (BQinv v).
  move:(pa' _ vx) => vp; move:(QpsS_inv vp) => ivp.
  apply/setC_P; split; first by apply:BQps_sBQ.
   move => /setC_P [_] []; apply/funI_P; ex_tac.
  by apply/(BQinv_mon2 (pa' _ ux) (pa' _ vx)). 
Qed.


Lemma BRinv_K x: realp x -> BRinv (BRinv x) = x.
Proof.
wlog xp: x / inc x BRps.
  move => H xr; case /BR_i1P:(xr) => sx.
  + by rewrite sx !BRinv_0.
  + by apply:H.
  + move:(RSo xr) => h.
    move: (f_equal BRopp (H _ (BRopp_negative1 sx) h)).
    by rewrite - (BRinv_opp (RS_inv h)) - (BRinv_opp h) (BRopp_K xr).
case/BR_rational_dichot => rx.
  move/BR_of_Q_prop2: rx => [y yq ->]. 
  by rewrite (BRinv_Q yq) (BRinv_Q (QS_inv yq)) (BQinv_K yq).
move:(RpsS_inv xp) (RIS_inv rx).
rewrite (BRinv_irrational rx) => ha h; rewrite (BRinv_irrational h).
rewrite (Y_true ha) (Y_true xp); clear h ha.
set_extens t.
  move => /setC_P[tp h];ex_middle tnx; case:h.
  have e1 :=(BQinv_K (BQps_sBQ tp)).
  apply/funI_P; rewrite - e1; exists (BQinv t) => //.
  apply/setC_P; split; [ apply: (QpsS_inv tp) | move => /funI_P [z zx zv]].
  by case: tnx; rewrite (BQinv_inj (BQps_sBQ tp) (BRi_sQ (BRps_sBR xp) zx) zv).
move => tx; move:((proj1 (BR_hi_Qps' xp)) _ tx) => tp.
apply/setC_P; split =>// /funI_P [ z /setC_P [za zb] zc]; case: zb.
by apply/funI_P; ex_tac; rewrite zc (BQinv_K (BQps_sBQ za)).
Qed.

Lemma BRinv_eq0 x: realp x -> BRinv x = \0r -> x = \0r.
Proof. by move => xr hr; move:(BRinv_K xr); rewrite hr BRinv_0. Qed.

Lemma BRinv_inj x y: realp x -> realp y -> BRinv x = BRinv y -> x = y.
Proof. by move => /BRinv_K e1 /BRinv_K e2 e3; rewrite - e1 - e2 e3. Qed.


Lemma BRinv_1: BRinv \1r = \1r. 
Proof. by move:(BRinv_Q QS1); rewrite BQinv_1. Qed.


Lemma BRinv_m1: BRinv \1mr = \1mr. 
Proof. by move:(BRinv_Q QSm1); rewrite BQinv_m1. Qed.

Lemma BRinv_2: BRinv \2r = \2hr. 
Proof. by move:(BRinv_Q QS2); rewrite BQinv_2. Qed.


Lemma BRprod_inv1 x : realp x -> x <> \0r -> (x *r (BRinv x)) = \1r.
Proof. 
wlog xp:x /(inc x BRps).
  move => H xq xns;case /BR_i1P:(xq) => xs //; first by apply:H.
  move: (BRopp_negative1 xs) => oxp; move:(BRps_sBR oxp) => oxr.
  rewrite -(BRprod_opp_opp xq (RS_inv xq)) - (BRinv_opp xq); apply: H => //.
  by move /BRps_iP:oxp => [_ ].
case/BR_rational_dichot => rx.
  move/BR_of_Q_prop2: rx => [y yq ->] h.
  rewrite (BRinv_Q yq) (BRprod_cQ yq (QS_inv yq)) (BQprod_inv1) //.
  by dneg h1; rewrite h1.
move => _.
rewrite (BR_prod_aux1 xp (RpsS_inv  xp)).
rewrite (BRinv_irrational rx)(Y_true xp).
move:(rx) => [[pa pb pc pd pe] pf].
set_extens t.
  move/BR_prod_auxP => [z zx [u /setC_P [up uix] ->]].
  suff h: \1q <q z *q u. apply/Zo_P; split => //; exact:(proj32_1 h).
  move:(BRi_sQ (BRps_sBR xp) zx) => zq.
  have uq:= (BQps_sBQ up).
  have unz:= (BQps_nz up).
  have uiq:= QS_inv uq.
  apply/(BQprod_plt2r QS1 (QSp zq uq) (QpsS_inv up)).
  rewrite (BQprod_1l uiq) -/(_ /q _) BQprodC BQdiv_prod //.
  case:(qleT_el zq uiq) => // zu; case: uix.
  apply/funI_P;exists (BQinv u); last by rewrite BQinv_K.
  case: (equal_or_not (BQinv u) z) => uz; first by rewrite uz.
  apply: (pd _ _ zx (conj zu (nesym uz))).
move => /Zo_P[tq t1]; apply/BR_prod_auxP.
have tp: inc t BQps. by have lt01:=qlt_01; apply/  qlt0xP; BQo_tac.
have[w wx wp]: exists2 w, ~inc w x & \0q <q w.
  move:(setC_ne (BR_hi_Qps' xp)) => [w /setC_P [/ qlt0xP sa sb]].
  by exists w.
set delta := w *q (\1q -q BQinv t).
have itq:=(QS_inv tq).
have itp: inc (\1q -q BQinv t) BQps.
  apply / qlt0xP/ (qlt_diffP1 itq QS1). 
  by move/(BQinv_mon2 tp QpsS1): t1; rewrite BQinv_1.
have dp: inc delta BQps  by apply:QpsS_prod; [ apply/ qlt0xP | ].
have  [y yx yv] := (BRi_lowbound (BRps_sBR xp) dp).
have yq := (pa _ yx).
have yp:= (BR_hi_Qps (BRps_sBRp xp) yx).
have ynz:=BQps_nz  yp.
exists y => //; exists (t /q y); last by rewrite BQprod_div.
apply/setC_P; split;first by apply:QpsS_div. 
move => /funI_P [z zx zv].
case: (qleT_ell (BQps_sBQ yp)  (proj32_1 wp)) => wy.
    by case: wx; rewrite - wy.
  case: wx; apply:(pd _ _ yx wy).
move /(BQprod_Mltgt0 itp): wy; rewrite -/delta. 
rewrite (BQprodBr yq QS1 itq) (BQprod_1r yq).
rewrite -/(_ /q _)-(BQinv_div tq yq) zv (BQinv_K (pa _ zx)) => la.
move/(BQsum_lt2r (proj31_1 la)(proj32_1 la) (pa _ zx)): la.
rewrite (BQsum_diff1 (pa _ zx) yq) => lb.
have lc:=(yv _ zx).
move/(BQsum_lt2l (proj31_1 lc)(proj32_1 lc) (BQps_sBQ dp)): lc.
rewrite (BQsum_diff (BQps_sBQ dp) yq); move => [ld _]; BQo_tac.
Qed.

Lemma BR_one_nz: \1r <> \0r.
Proof. by move/ rlt0xP: RpsS1 => [ _ /nesym]. Qed.

Lemma BR_inv_prop a b: realp a -> realp b -> a *r b = \1r -> b = BRinv a.
Proof.
move => ar br h.
have ha:= RS_inv ar.
case: (equal_or_not a \0r) => aq.
  by move: h; rewrite aq BRprod_0l // => hh; case:BR_one_nz.
move: (f_equal (fun z => (BRinv a) *r z) h). 
rewrite BRprodA // BRprod_1r // (BRprodC _ a) (BRprod_inv1) // BRprod_1l //.
Qed.

Lemma BRprod_inv x y:realp x -> realp y ->
   BRinv (x *r y) = BRinv x *r BRinv y.
Proof.
move => xr yr.
have pc :=RS_inv xr.
have pd :=RS_inv yr.
case: (equal_or_not x \0r) => xz.
   by rewrite xz BRinv_0 BRprod_0l BRinv_0 BRprod_0l.
case: (equal_or_not y \0r) => yz.
  by rewrite yz BRinv_0 BRprod_0r BRinv_0 BRprod_0r.
symmetry; apply:BR_inv_prop; try apply:RSp => //.
rewrite BRprod_ACA // !BRprod_inv1 // BRprod_1l //; apply: RS1.
Qed.

Definition BRdiv x y := x *r  (BRinv y).

Notation "x /r y" := (BRdiv x y) (at level 40).

Lemma RS_div x y: realp x -> realp y -> realp (x /r y).
Proof. by move => xr /RS_inv yr; apply:RSp. Qed.

Lemma BRdiv_0x x : \0r /r x = \0r.
Proof. apply: BRprod_0l. Qed.

Lemma BRdiv_x0 x : x /r \0r = \0r.
Proof. by rewrite /BRdiv BRinv_0 BRprod_0r. Qed.


Lemma BRdiv_1x x : realp x -> \1r /r x = BRinv x.
Proof. move => xr; apply: (BRprod_1l (RS_inv xr)). Qed.

Lemma BRdiv_x1 x : realp x -> x /r \1r = x.
Proof. by move => xr; rewrite /BRdiv BRinv_1 BRprod_1r. Qed.


Lemma RpsS_div a b: inc a BRps -> inc b BRps -> inc (a /r b) BRps.
Proof.
move => ap bp; apply:RpsS_prod => //; exact: (RpsS_inv bp).
Qed.

Lemma RmsuS_div a b: inc a BRms -> inc b BRms -> inc (a /r b) BRps.
Proof.
move => ap bp; apply:RmsuS_prod => //; exact: (RmsS_inv bp).
Qed.


Lemma RpmsS_div a b: inc a BRps -> inc b BRms -> inc (a /r b) BRms.
Proof.
move => ap bp; apply:RpmsS_prod => //; exact: (RmsS_inv bp).
Qed.

Lemma RmpsS_div a b: inc a BRms -> inc b BRps -> inc (a /r b) BRms.
Proof.
move => ap bp; rewrite /BRdiv BRprodC.
apply:RpmsS_prod => //;exact: (RpsS_inv bp).
Qed.

Lemma RpS_div a b: inc a BRp -> inc b BRp -> inc (a /r b) BRp.
Proof.
move: RpS0 => izp ap bp.
case: (equal_or_not a \0r) => az; first by rewrite az BRdiv_0x. 
case: (equal_or_not b \0r) => bz; first by rewrite bz BRdiv_x0.
by apply/(BRps_sBRp); apply:RpsS_div; apply/BRps_iP.
Qed.

Lemma RmuS_div a b: inc a BRm -> inc b BRm -> inc (a /r b) BRp.
Proof.
move: RpS0 => izp ap bp.
case: (equal_or_not a \0r) => az; first by rewrite az BRdiv_0x. 
case: (equal_or_not b \0r) => bz; first by rewrite bz BRdiv_x0. 
by apply/(BRps_sBRp); apply:RmsuS_div; apply/BRms_iP.
Qed.

Lemma BRpmS_div a b: inc a BRp -> inc b BRm -> inc (a /r b) BRm.
Proof.
move: RmS0 => izp ap bp.
case: (equal_or_not a \0r) => az; first by rewrite az BRdiv_0x.
case: (equal_or_not b \0r) => bz; first by rewrite bz BRdiv_x0.
by apply/(BRms_sBRm); apply:RpmsS_div; [apply/BRps_iP | apply/BRms_iP ].
Qed.


Lemma BRmpS_div a b: inc a BRm -> inc b BRp -> inc (a /r b) BRm.
Proof.
move: RmS0 => izp ap bp.
case: (equal_or_not a \0r) => az; first by rewrite az BRdiv_0x.
case: (equal_or_not b \0r) => bz; first by rewrite bz BRdiv_x0.
by apply/(BRms_sBRm); apply:RmpsS_div; [ apply/BRms_iP | apply/BRps_iP ].
Qed.



Lemma BRopp_div_r x y: realp x -> realp y ->
  BRopp (x /r y) = x /r (BRopp y).
Proof. 
move => xr yr; rewrite /BRdiv (BRinv_opp yr) BRopp_prod_r //; exact: RS_inv.
Qed.

Lemma BRopp_div_l x y: realp x -> realp y ->
  BRopp (x /r y) = (BRopp x) /r y.
Proof. 
move => xr yr; rewrite /BRdiv BRopp_prod_l //; exact: RS_inv.
Qed.

Lemma BRdiv_opp_comm x y: realp x -> realp y ->
  x /r  (BRopp y) =  (BRopp x) /r y.
Proof. by move => xr yr; rewrite - BRopp_div_l // BRopp_div_r. Qed.

Lemma BRdiv_opp_opp x y: realp x -> realp y ->
  (BRopp x) /r (BRopp y) = x /r y.
Proof. 
move => xr yr.
by rewrite -(BRopp_div_l xr (RSo yr)) - BRopp_div_r // BRopp_K //; apply:RS_div.
Qed.

Lemma BRdiv_xx x : realp x -> x <> \0r -> (x /r x) = \1r.
Proof. apply:BRprod_inv1. Qed.

Lemma BQ_ltinv1 x: inc x BRps ->
   (x <r \1r <-> \1r <r BRinv x).
Proof.
move => h.
move/BRps_iP: (h) => [/BRp_sBR xr xnz].
have h0: BRinv x *r x = \1r by rewrite BRprodC (BRprod_inv1 xr xnz).
move:(BRps_sBRp (RpsS_inv h)) => h2.
split => h1.
  case:(rleT_ell RS1 (BRp_sBR h2)) => // h3.
    by case: (proj2 h1);move:(BRinv_K xr); rewrite - h3 BRinv_1.
  by move:(proj2 (BRprod_Mltltgt0 RpsS1 h h3 h1)); rewrite h0 (BRprod_1r RS1).
case:(rleT_el RS1 xr) => // h3.
by move: (proj2 (BRprod_Mltpp h2 h3 h1)); rewrite h0.
Qed.

Lemma BR_square_1 x: realp x -> 
   (x *r x = \1r <-> (x = \1r \/ x = \1mr)).
Proof.
move => xr; split => eq; last first.
  case:eq => ->;first by rewrite (BRprod_1r RS1). 
  by rewrite (BRprod_m1r RSm1) BRopp_m1.
suff H: forall x, inc x BRps ->  x *r x = \1r -> x = \1r.
  case/BR_i1P: xr => ha.
  + by left;move: eq; rewrite ha BRprod_0r.
  + by left; apply: H.
  + right; move:(BRms_sBR ha) => hb.
    move: (BRprod_opp_opp hb hb); rewrite eq => hc.
    move:(f_equal BRopp (H _ (BRopp_negative1 ha) hc)).
    by rewrite (BRopp_K hb) BRopp_1.
move => y yp eq1; move:(BRps_sBR yp) => yr.
move:(BR_inv_prop yr yr eq1) => h1.
case: (rleT_ell (BRps_sBR yp) RS1) => // h2.
  move/(BQ_ltinv1 yp): (h2); rewrite - h1; move =>[h3 _]; BRo_tac.
move:(h2); rewrite h1; move/(BQ_ltinv1 yp) => [h3 _]; BRo_tac.
Qed.

Lemma BR_self_inv x: realp x ->
   (x = BRinv x <-> [\/ x= \0r, x = \1r | x = \1mr]).
Proof.
move => xr; split.
   move => h; case: (equal_or_not x \0r) => e0; first by constructor 1. 
   move: (f_equal (fun z => x *r z) h).
   rewrite (BRprod_inv1 xr e0) => /(BR_square_1 xr).
   by case => hh;[constructor 2 | constructor 3].
by case => ->; [rewrite BRinv_0 | rewrite BRinv_1 | rewrite BRinv_m1 ].
Qed.


Lemma BRdiv_square a b: realp a -> realp b -> 
    BRsquare (a /r b) = (BRsquare a) /r (BRsquare b).
Proof.
move => ar br; rewrite /BRsquare /BRdiv.
have ibr:= (RS_inv br).
rewrite (BRprod_ACA ar ibr ar ibr).
by rewrite (BRprod_inv br br).
Qed.



Lemma BRdiv_sumDl x y z: realp x -> realp y -> realp z ->
   (y +r z) /r x = (y /r x) +r (z /r x).
Proof. move => xr yr zr;rewrite /BRdiv BRprodDl //; exact:RS_inv. Qed.

Lemma BRdiv_prod_simpl_l x y z: realp x -> realp y -> realp z ->
   x <> \0r ->  (x *r y) /r  (x *r z) = y /r z.
Proof.
move => xr yr zr xnz.
rewrite /BRdiv (BRprod_inv xr zr) (BRprodC x y).
rewrite (BRprodA (RSp yr xr) (RS_inv xr) (RS_inv zr)).
by rewrite  -(BRprodA yr xr (RS_inv xr))  BRprod_inv1 // BRprod_1r.
Qed.

Lemma BRdiv_prod_comm x y z: realp x -> realp y -> realp z ->
  (x *r y) /r z = (x /r z) *r y.
Proof. 
move => xr yr zr.
rewrite /BRdiv (BRprodC x y) (BRprodC _ y) - (BRprodA yr xr) //; exact:RS_inv.
Qed.


Lemma BRinv_div x y: realp x -> realp y ->  BRinv (x /r y) = y /r x.
Proof.
move => xr yr.
by rewrite /BRdiv (BRprod_inv xr (RS_inv yr)) (BRinv_K yr) BRprodC.
Qed.

Lemma BRdiv_prod x y:realp x -> realp y ->  x <> \0r -> (x *r y) /r x = y.
Proof. 
move => xr yr h.
rewrite /BRdiv BRprodC (BRprodA (RS_inv xr) xr yr).
by rewrite (BRprodC _ x)  BRprod_inv1 // BRprod_1l.
Qed.

Lemma BRprod_div x y: realp x -> realp y -> x <> \0r -> x *r (y /r x) = y.
Proof. 
move => xr yr h.
by rewrite/BRdiv (BRprodC y)(BRprodA xr (RS_inv xr) yr) BRprod_inv1// BRprod_1l.
Qed.

Lemma BRprod_div1 x y: realp x -> realp y -> x <> \0r -> (y /r x) *r x = y.
Proof. by move => xr yr h; rewrite BRprodC; apply:BRprod_div. Qed.

Lemma BRprod_div_ea x y z: realp x -> realp y -> realp z ->
   y <> \0r -> x = y *r z -> z = x /r y.
Proof. by move => xy yr zr h -> ; rewrite BRdiv_prod. Qed.

Lemma BRdiv_diag_rw x y: realp x -> realp y ->  x /r y = \1r -> x = y.
Proof. 
move => xr yr h. 
case: (equal_or_not y \0r) => h'.
   by move: h; rewrite h' (BRdiv_x0) => hh; case: BR_one_nz.
by move:(f_equal (BRprod y) h); rewrite (BRprod_div yr xr h') BRprod_1r.
Qed.

Lemma BRdiv_prod_simpl_r x y z: realp x -> realp y -> realp z -> z <> \0r ->
  (x *r z) /r (y *r z) = x /r y.
Proof.  
move => xr yr rz h; rewrite (BRprodC x z) (BRprodC y z).  
by apply: BRdiv_prod_simpl_l.
Qed.

Lemma BRprod_eq2r x y z: realp x -> realp y -> realp z -> z <> \0r ->
    x *r z = y *r z -> x = y.
Proof.
move => xr yr zr zp h.
by rewrite - (BRdiv_prod zr xr zp) - (BRdiv_prod zr yr zp) BRprodC h BRprodC.
Qed.

Lemma BRprod_eq2l x y z: realp x -> realp y -> realp z -> z <> \0r ->
   z *r x = z *r y -> x = y.
Proof.
rewrite (BRprodC z) (BRprodC z); apply: BRprod_eq2r.
Qed.

Lemma BRdiv_div_simp a b c: realp a -> realp b -> realp c -> b <> \0r ->
    (a /r b) /r (c /r b) = a /r c.
Proof.
move => ar br cr bnz. 
move: (RS_inv br)  (RS_inv cr) => bir cir.
rewrite /BRdiv (BRinv_div cr br) (BRprodC a).
rewrite (BRprod_ACA bir ar br cir) (BRprodC  _ b) BRprod_inv1 //.
by rewrite BRprod_1l //; apply:RSp.
Qed.


Lemma BRsum_div a b c: realp a -> realp b -> realp c -> c <> \0r ->
   a +r (b /r c) = (a *r c +r b) /r c.
Proof.
move => ar br cr cnz.
have {1} -> : a = (a *r c) /r c by rewrite BRprodC BRdiv_prod //.
by rewrite - BRprodDl //; [ apply:RS_inv| apply:RSp].
Qed.


Lemma BRdiff_div a b c: realp a -> realp b -> realp c -> c <> \0r ->
   a -r (b /r c) = (a *r c -r b) /r c.
Proof.
move => ar br cr cnz.
by rewrite /BRdiff (BRopp_div_l br cr);  apply: BRsum_div => //; apply:RSo.
Qed.

Lemma BRinv_diff x y: realp x -> realp y ->x <> \0r -> y <> \0r ->
 (BRinv x -r BRinv y) = (y -r x) /r (x *r y).
Proof.
move => xr yr xnz ynz.
move:(RS_inv xr)(RS_inv yr) (RSp xr yr) (RS_diff yr xr) => ixr iyr xyr dr.
move:(BRprod_nz xr yr xnz ynz) => xynz.
apply:(BRprod_eq2r (RS_diff ixr iyr) (RS_div dr xyr) xyr xynz).
rewrite (BRprod_div1 xyr dr xynz) (BRprodBl xyr ixr iyr).
rewrite BRprodC  -/(_ /r _) (BRdiv_prod xr yr xnz).
by rewrite BRprodC  -/(_ /r _)(BRprodC x y) (BRdiv_prod yr xr ynz).
Qed.

Lemma BRdiv_Mlelege0 a b c d: 
   realp a -> inc b BRps -> realp c -> inc d BRps ->
   ( a /r b <=r c /r d <-> a *r d <=r b *r c).
Proof.
move => ar brps cr drps.
move/ BRps_iP: (brps) => [/BRp_sBR br bnz].
move/ BRps_iP: (drps) => [/BRp_sBR dr dnz].
have idr:=RS_inv dr. 
have pb:=RSp cr br.  
have pa:=RSp pb idr. 
move:(BRprod_Mgt0le (RS_div ar br) (RS_div cr dr) brps).
rewrite (BRprod_div br ar bnz) (BRprodA br cr idr) (BRprodC b).
move:(BRprod_ple2r ar pa drps).
rewrite  -/(_ /r d) (BRprodC ((c *r b) /r d)) (BRprod_div dr pb dnz).
move => sa sb; exact:(iff_sym(iff_trans sa sb)).
Qed.


Lemma BRdiv_Mltltge0 a b c d: 
   realp a -> inc b BRps -> realp c -> inc d BRps ->
   ( a /r b <r c /r d <-> a *r d <r b *r c).
Proof.
move => ar brps cr drps.
move/ BRps_iP: (drps) => [/BRp_sBR dr dnz].
move/ BRps_iP: (brps) => [/BRp_sBR br bnz].
have qr: realp (BRinv d) by apply:RS_inv.
split; move => [sa sb];split.
+ by apply/(BRdiv_Mlelege0 ar brps cr drps).
+ dneg h; move: (f_equal (fun z => z /r d) h).
  rewrite BRprodC (BRdiv_prod dr ar dnz) => ->.
  by rewrite {2} /BRdiv - BRprodA // BRdiv_prod //; apply:RSp.
+ by apply/(BRdiv_Mlelege0 ar brps cr drps).
+ dneg h; move: (f_equal (fun z => z *r b) h).
  rewrite BRprodC BRprod_div // => ->.
  rewrite /BRdiv (BRprodC c)- (BRprodA qr cr br) (BRprodC (BRinv d)).
  by rewrite BRprodC (BRprodC b); apply: BRprod_div => //; apply:RSp.
Qed.


Lemma BRinv_mon a b: inc a BRps -> inc b BRps  ->
   (\1r /r a <=r \1r /r b <-> b <=r a).
Proof.
move => pa pb; move: (BRps_sBR pa)(BRps_sBR pb) => ar br.
move: (BRdiv_Mlelege0 RS1 pa RS1 pb); rewrite BRprod_1l // BRprod_1r //. 
Qed.

Lemma BRinv_mon1 a b: inc a BRps -> inc b BRps  ->
   (BRinv a <=r BRinv b <-> b <=r a).
Proof.
move => pa pb.
rewrite - (BRdiv_1x (BRps_sBR pa)) - (BRdiv_1x (BRps_sBR pb)).
apply: (BRinv_mon pa pb).
Qed.

Lemma BRinv_mon2 a b: inc a BRps -> inc b BRps ->
   (BRinv a <r BRinv b <-> b <r a).
Proof.
move => pa pb; split; move => [ha hb]; split.
+ by apply /BRinv_mon1.
+ by dneg h; rewrite h.
+ by apply /BRinv_mon1.
+ by move /(BRinv_inj  (BRps_sBR pa) (BRps_sBR pb)) => /nesym.
Qed.

Lemma BRdiv_Mle1 a b c: realp a -> realp b -> inc c BRps ->
     ( a <=r b *r c <->  a /r c <=r b).
Proof.
move => ar br crp; move:(RpsS_inv crp) => ip.
move/BRps_iP: (crp) => [/BRp_sBR cp cnz].
split => h.  
  move:  (BRprod_Mlege0 (BRps_sBRp ip) h).
  rewrite (BRprodC b) -! /(BRdiv _ _)  BRdiv_prod //.
move:  (BRprod_Mlege0 (BRps_sBRp crp) h).
rewrite BRprodC BRprod_div //.
Qed.



(** abs *)


Definition BRabs x:= Yo (inc x BRp) x (BRopp x).

Lemma BRabs_pos x: inc x BRp -> BRabs x = x.
Proof. by move => h; rewrite/BRabs (Y_true h). Qed.

Lemma BRabs_poss x: inc x BRps -> BRabs x = x.
Proof. by move /BRps_sBRp => /BRabs_pos. Qed.


Lemma BRabs_0 : BRabs \0r = \0r.
Proof. exact: (BRabs_pos RpS0). Qed.

Lemma BRabs_negs x: inc x BRms -> BRabs x = BRopp x.
Proof.  by move => /BR_di_neg_pos h; rewrite /BRabs (Y_false h). Qed.

Lemma BRabs_neg x: inc x BRm -> BRabs x = BRopp x.
Proof. 
case (equal_or_not x \0r) => e1.
  by rewrite e1 BRopp_0 BRabs_0.
by move => h; apply:BRabs_negs; apply /BRms_iP.
Qed.

Lemma RpSa x: realp x -> inc (BRabs x) BRp.
Proof.
case/BR_i0P => h; last by rewrite (BRabs_pos h).
rewrite (BRabs_negs h); apply: (BRopp_negative2 (BRms_sBRm h)).
Qed.

Lemma RSa x: realp x -> realp (BRabs x).
Proof. by move => /RpSa => h;apply:BRp_sBR. Qed.

Lemma BRabs_abs x: realp x -> BRabs (BRabs x) = BRabs x.
Proof. by move => /RpSa /BRabs_pos. Qed.

Lemma BRabs_opp x: realp x -> BRabs (BRopp x) = BRabs x.
Proof. 
case/BR_i1P => h.
+ by rewrite h BRopp_0.
+ by rewrite (BRabs_negs (BRopp_positive1 h)) (BRopp_K (BRps_sBR h))BRabs_poss.
+ by rewrite (BRabs_poss (BRopp_negative1 h)) (BRabs_negs h).
Qed.

Lemma BRabs_m1: BRabs \1mr = \1r.
Proof. by rewrite (BRabs_negs RmsSm1) BRopp_m1. Qed.

Lemma BRabs_1: BRabs \1r = \1r.
Proof. exact (BRabs_poss RpsS1). Qed.

Lemma BRabs0_bis x: realp x ->  (x = \0r <-> BRabs x = \0r).
Proof.
move => pa; split; first by  move => ->; rewrite BRabs_0.
case/BR_i0P:pa => h; last by rewrite (BRabs_pos h). 
move: RS0 => rs0.
by rewrite (BRabs_negs h) - {1} BRopp_0; apply: BRopp_inj => //;apply:BRms_sBR.
Qed.

Lemma RpsSa x: realp x -> x <> \0r -> inc (BRabs x) BRps.
Proof.
move => xr xnz. 
by apply/BRps_iP; split;[ apply:(RpSa xr) |apply/(BRabs0_bis xr)].
Qed.

Lemma BRabs_cQ x: ratp x ->
  BRabs (BR_of_Q x) = BR_of_Q (BQabs x). 
Proof.
move => h; case /BQ_i1P: (h) => ha.
+ by rewrite ha BQabs_0 BRabs_0.
+ by rewrite (BQabs_pos (BQps_sBQp ha)) BRabs_poss //; apply:RpsS_of_Q. 
+ by rewrite (BQabs_negs ha) (BRabs_negs (RmsS_of_Q ha)) BRopp_Q.
Qed.


Lemma BRprod_abs x y: realp x -> realp y ->  
  BRabs (x *r y) = (BRabs x) *r (BRabs y).
Proof. 
move => xr yr.
case /BR_i0P: (xr)=> pa; case /BR_i0P: (yr)=> pb.
+ rewrite (BRabs_negs pa) (BRabs_negs pb) (BRprod_opp_opp xr yr).
  by rewrite (BRabs_poss (RmsuS_prod pa pb)).
+ rewrite (BRabs_negs pa) (BRabs_pos pb) - (BRopp_prod_l xr yr).
  by rewrite BRprodC (BRabs_neg (RpmS_prod pb (BRms_sBRm pa))).
+ rewrite (BRabs_negs pb) (BRabs_pos pa) - (BRopp_prod_r xr yr).
  by rewrite  (BRabs_neg (RpmS_prod pa (BRms_sBRm pb))).
+ by rewrite (BRabs_pos pa) (BRabs_pos pb) (BRabs_pos (RpS_prod pa pb)).
Qed.


Lemma BRinv_abs x: realp x -> BRabs (BRinv x) = BRinv (BRabs x).
Proof. 
move => xr.
case/BR_i1P: (xr) => h.
+ by rewrite h BRabs_0 BRinv_0 BRabs_0.
+ by rewrite (BRabs_pos (BRps_sBRp(RpsS_inv h))) (BRabs_pos (BRps_sBRp h)).
+ by rewrite (BRabs_negs (RmsS_inv h)) (BRabs_negs h) (BRinv_opp xr).
Qed.

Lemma BRdiv_abs x y: realp x -> realp y ->
  (BRabs x) /r (BRabs y) = BRabs (x /r y).
Proof. 
move => xr yr.
by rewrite /BRdiv (BRprod_abs xr (RS_inv yr))  (BRinv_abs yr).
Qed.

Lemma rle_abs x: realp x -> x <=r (BRabs x).
Proof. 
move => xr;case /BR_i0P: (xr) => xp.
  move: (RpSa xr) => / rle0xP pa; move / rgt0xP: xp => [pb _]; BRo_tac.
by rewrite (BRabs_pos xp); apply:rleR.
Qed.

Lemma BRabs_diff a b: realp a -> realp b ->
   BRabs (a -r b) = BRabs (b -r a).
Proof.
by move => ar br; rewrite - (BRoppB br ar) (BRabs_opp (RS_diff br ar)). 
Qed.

Lemma rle_triangular x y: realp x -> realp y -> 
  (BRabs (x +r y)) <=r (BRabs x) +r (BRabs y).
Proof.
move: x y.
pose aux n m := BRabs (n +r m) <=r BRabs n +r BRabs m.
suff: forall n m, inc n BRp -> inc m BR -> aux n m.
  move => h n m; case /BR_i0P; last by apply: h.
  move => pa pb; move: (BRms_sBR pa) => pc.
  rewrite - (BRabs_opp (RSs pc pb)) - (BRabs_opp pb) -(BRabs_opp pc).  
  rewrite (BRoppD pc pb); apply: h (RSo pb).
  apply:BRopp_negative2 (BRms_sBRm pa).
move => n m np; case  /BR_i0P; last first.
  move => mp; rewrite /aux (BRabs_pos np) (BRabs_pos mp).
  move:(RpS_sum np mp) => pa; move: (BRp_sBR pa) => pb.
  rewrite (BRabs_pos pa); apply: (rleR pb).
move => mn; rewrite /aux.
move: (BRp_sBR np) (BRms_sBR mn) => nq mq.
have pa : \0r <=r BRabs n +r BRabs m.
  by apply / rle0xP; apply: (RpS_sum);apply: RpSa.
case /BR_i1P: (RSs nq mq) => sa.
+ by rewrite sa BRabs_0.
+ rewrite (BRabs_poss sa).
  move: (rle_abs mq); rewrite (BRabs_pos np).
 by move /(BRsum_le2l mq (RSa mq) nq).
+ rewrite (BRabs_negs sa) (BRabs_pos np)  (BRabs_negs mn).
  rewrite (BRoppD nq mq). 
  apply/(BRsum_le2r (RSo nq) nq (RSo mq)).
  move / rge0xP: (BRopp_positive2 np) => sb.
  move/ rle0xP: np => sc; BRo_tac.
Qed.


Lemma BRabs_prop2 x y: realp x -> realp y ->
  (BRabs x <r y <->  (BRopp y <r x /\ x <r y)).
Proof.
move => xr yr.
case /BR_i0P: (xr) => xp.
   rewrite (BRabs_negs xp); move: (rlt_oppP (RSo xr) yr);rewrite (BRopp_K xr).
   move => h;apply:(iff_trans (iff_sym h)); split; last by move => [].
   move => h1; split => //.
   move:(BRms_sBRm xp) => xp'.
   move:(rle_par3 (BRopp_negative2 xp') xp') => h2.
   move/h: h1 => h3; BRo_tac.
rewrite (BRabs_pos xp); split; last by move => [].
move => lxy; split => //; rewrite - (BRopp_K xr); apply: rlt_opp.
have h: BRopp x <=r x by apply:(rle_par3 xp (BRopp_positive2 xp)).
BRo_tac.
Qed.

Lemma BRabs_prop1 x y: realp x -> realp y ->
  (BRabs x <=r y <->  (BRopp y <=r x /\ x <=r y)).
Proof.
move => xr yr.
case /BR_i0P: (xr) => xp.
   rewrite (BRabs_negs xp); move: (rle_oppP (RSo xr) yr);rewrite (BRopp_K xr).
   move => h. apply:(iff_trans (iff_sym h)); split; last by move => [].
   move => h1; split => //.
   move:(BRms_sBRm xp) => xp'.
   move:(rle_par3 (BRopp_negative2 xp') xp') => h2.
   move/h: h1 => h3; BRo_tac.
rewrite (BRabs_pos xp); split; last by move => [].
move => lxy; split => //; rewrite - (BRopp_K xr); apply: rle_opp.
have h: BRopp x <=r x by apply:(rle_par3 xp (BRopp_positive2 xp)).
BRo_tac.
Qed.

Lemma BRabs_prop3 x y e: realp x -> realp y -> realp e ->
  (BRabs (x -r y) <=r e <->  y -r e <=r x /\ x <=r y +r e).
Proof.
move => xr yr er.
have Ha: BRopp e <=r x -r y <-> y -r e <=r x.
  rewrite - (BRoppB yr xr).
  exact (iff_trans (rle_oppP (RS_diff yr xr) er) (BRdiff_le1P yr xr er)).
have Hb: x -r y <=r e <->  x <=r y +r e.
  move:(BRsum_le2r xr (RSs yr er) (RSo yr)). 
  by rewrite -/(_ -r _)  -/(_ -r _)  (BRdiff_sum yr er).
move:(BRabs_prop1 (RS_diff xr yr) er) => H.
split; first by move/H => [/Ha ha /Hb hb].
by move => [/Ha ha /Hb hb]; apply/H.
Qed.


Lemma BRabs_prop4 x y e: realp x -> realp y -> realp e ->
  (BRabs (x -r y) <r e <->  y -r e <r x /\ x <r y +r e).
Proof.
move => xr yr er.
have Ha: BRopp e <r x -r y <-> y -r e <r x.
  rewrite - (BRoppB yr xr).
  exact (iff_trans (rlt_oppP (RS_diff yr xr) er) (BRdiff_lt1P yr xr er)).
have Hb: x -r y <r e <->  x <r y +r e.
  move:(BRsum_lt2r xr (RSs yr er) (RSo yr)). 
  by rewrite -/(_ -r _)  -/(_ -r _)  (BRdiff_sum yr er).
move:(BRabs_prop2 (RS_diff xr yr) er) => H.
split; first by move/H => [/Ha ha /Hb hb].
by move => [/Ha ha /Hb hb]; apply/H.
Qed.




(** ** half and middle *)

Definition BRhalf x := x *r \2hr.
Definition BRmiddle x y := BRhalf (x +r y).
Definition BRdouble x := \2r *r x.

Lemma RSdouble x: realp x -> realp (BRdouble x).
Proof. by move: RS2 => sa sb; apply:RSp. Qed.
 
Lemma BRdouble_C x : BRdouble x = x *r \2r.
Proof. apply: BRprodC. Qed.

Lemma BRdouble_s x: realp x -> x +r x = x *r \2r.
Proof.
move: RS1 => rs1 xr.
by rewrite - {1 2} (BRprod_1r xr) - BRsum_11 (BRprodDr).
Qed.

Lemma BRdouble_half2:  \2hr +r \2hr = \1r.
Proof.
rewrite (BRdouble_s RSh2) - BRinv_2 BRprodC; apply:(BRdiv_xx RS2).
exact: BR2_nz.
Qed.

Lemma RS_half x:  realp x -> realp (BRhalf x).
Proof. move => h; apply (RSp h RSh2). Qed.

Lemma BR_middle x y: realp x -> realp y -> realp (BRmiddle x y).
Proof. move => xr yr; apply:(RS_half (RSs xr yr)). Qed.

Lemma BRdouble_half1 x: realp x -> BRhalf x +r BRhalf x = x.
Proof.
move => h.
by rewrite /BRhalf - (BRprodDr h RSh2 RSh2) BRdouble_half2 BRprod_1r.
Qed.


Lemma BRdouble_half x: realp x -> (BRhalf x) *r \2r = x.
Proof. 
by move => h; rewrite - (BRdouble_s (RS_half h)) (BRdouble_half1 h).
Qed.

Lemma BRhalf_double x: realp x -> BRhalf (x *r \2r) = x.
Proof.  
move => xr; rewrite BRprodC /BRhalf  - BRinv_2.  
apply:(BRdiv_prod RS2 xr BR2_nz).
Qed.

Lemma BRhalf_pos x: inc x BRps -> inc (BRhalf x) BRps. 
Proof. move => h; apply:(RpsS_prod h RpsSh2). Qed.

Lemma BRhalf_pos1 x: inc x BRps ->  (BRhalf x) <r x.
Proof.
move => h; move:(BRhalf_pos  h) => h1.
rewrite - {2} (BRdouble_half1 (BRps_sBR h)).
apply: (BRsum_Mps (BRps_sBR h1) h1).
Qed.

Lemma BRmiddle_comp x y: x <r y -> x <r BRmiddle x y /\  BRmiddle x y <r y.
Proof.
move => cp. 
move: (cp) => [[xr yr _] _].
split.
  have : x *r \2r <r x +r y.
    by rewrite - (BRdouble_s xr); apply /(BRsum_lt2l xr yr xr).
  move /(BRprod_plt2r (RSp xr RS2) (RSs xr yr) RpsSh2).
  by rewrite -/(BRhalf (x *r \2r)) (BRhalf_double xr).
have : x +r y <r y *r \2r.
  by rewrite - (BRdouble_s yr); apply /(BRsum_lt2r xr yr yr).
move /(BRprod_plt2r (RSs xr yr) (RSp yr RS2) RpsSh2).
by rewrite -/(BRhalf (y *r \2r)) (BRhalf_double yr).
Qed.

Lemma BRhalf_opp x: realp x -> BRhalf (BRopp x)  = BRopp (BRhalf x).
Proof.
by move => xr; rewrite /BRhalf BRopp_prod_l //; apply: RSh2.
Qed.

Lemma BRhalf_neg x: inc x BRms -> inc (BRhalf x) BRms. 
Proof. by move => h; move:(RpmsS_prod RpsSh2 h); rewrite BRprodC. Qed.

Lemma BR_middle_prop1 a b: realp a -> realp b ->
   b -r (BRmiddle a b) = BRhalf (b -r a).
Proof.
move => ar br; rewrite /BRmiddle -{1} (BRhalf_double br) /BRhalf.
rewrite - (BRprodBl RSh2 (RSp br RS2) (RSs ar br)) - (BRdouble_s br).
by rewrite BRdiff_sum_simpl_r.
Qed.

Lemma BR_middle_prop2 a b: realp a -> realp b ->
   (BRmiddle a b) -r a = BRhalf (b -r a).
Proof.
move => ar br.
rewrite /BRmiddle -{2} (BRhalf_double ar) /BQhalf.
rewrite - (BRprodBl RSh2 (RSs ar br)(RSp ar RS2)) - (BRdouble_s ar).
by rewrite BRdiff_sum_simpl_l.
Qed.


Lemma BRhalf_prop x: BRhalf x = x /r \2r.
Proof. by rewrite /BRhalf - BRinv_2. Qed.

Lemma BRhalf_mon x y : x <=r y -> BRhalf x <=r BRhalf y.
Proof.
move => h.
by move/(BRprod_ple2r (proj31 h) (proj32 h) RpsSh2):h.
Qed.

Lemma BRsum_square a b: realp a -> realp b ->
   BRsquare (a +r b) = BRsquare a +r BRsquare b +r BRdouble (a *r b). 
Proof.
move => ar br.
move:(RSp ar ar)(RSp br br)(RSp ar br)(RSs ar br) => aar bbr abr sabr.
rewrite {1}/BRsquare (BRprodDl sabr ar br).
rewrite (BRprodDr ar ar br) (BRprodDr br ar br) (BRprodC b a). 
rewrite (BRsumC (a *r b)) (BRsum_ACA aar abr bbr abr).
by rewrite  BRdouble_s //  BRdouble_C. 
Qed.

Lemma BRdiff_square a b: realp a -> realp b ->
   BRsquare (a -r b) = BRsquare a +r BRsquare b -r (BRdouble (a *r b)). 
Proof.
move => ar br.
rewrite (BRsum_square ar (RSo br)).
rewrite {2}/BRsquare (BRprod_opp_opp br br).
by rewrite /BRdouble - (BRopp_prod_r ar br) - (BRopp_prod_r RS2 (RSp ar br)).
Qed.

Lemma BRprod_22: \2r *r \2r = \4r.
Proof. move: QS2 => q2; rewrite BRprod_cQ // BQprod_22 //. Qed.

Lemma BRsumdiff_square a b: realp a -> realp b ->
   BRsquare (a +r b) = \4r *r (a *r b) +r BRsquare (a -r b). 
Proof.
move => ar br.
rewrite (BRdiff_square ar br) (BRsum_square ar br) - BRprod_22.
have ha := (RSp ar br).
move: (BRdouble_s (RSdouble ha)); rewrite - BRdouble_C /BRdouble =>  hb.
rewrite - (BRprodA RS2 RS2 ha) - hb.
set u := (BRsquare a +r BRsquare b); set v := (BRdouble (a *r b)).
have ur: realp u by apply:RSs; apply:RSp.
have vr: realp v by apply:RSdouble;apply:RSp.
rewrite (BRsum_ACA vr vr ur (RSo vr)) (BRsum_opp_r vr).
by rewrite BRsumC (BRsum_0r (RSs vr ur)).
Qed. 


Lemma BRsquare_diff x y: realp x -> realp y ->
   BRsquare x -r BRsquare  y = (x -r y) *r (x +r y).
Proof.
move => xr yr; move: (RSs xr yr) => sab.
rewrite BRprodBl //  !BRprodDr // (BRsumC (y *r x))  (BRprodC  y x).
by rewrite BRdiff_sum_simpl_r //; apply:RSp.
Qed.


Lemma BRsquare_inj x y: realp x -> realp y ->
   (BRsquare x = BRsquare  y  <->  (x = y \/ x = BRopp y)).
Proof.
move => xr yr.
move:(RSp yr yr)(RSs xr yr)(RS_diff xr yr) => sa sb sc.
split.
  move => h. 
  have: BRsquare x -r BRsquare  y = \0r by rewrite h (BRdiff_xx sa).
  rewrite (BRsquare_diff xr yr); move /(BRprod_nz_bis sc sb); case.
    by move/(BRdiff_xx_rw xr yr) ; left.
  by rewrite -{1} (BRopp_K yr); move/(BRdiff_xx_rw xr (RSo yr)); right.
by case => -> //; rewrite /BRsquare; apply: BRprod_opp_opp.
Qed.

(* plus haut *) 
Definition rmin x y := Yo (x <=r y) x y.

Lemma rmin_prop1 x y (r := rmin x y): realp x ->  realp y ->
  [/\ realp r, r <=r x & r <=r y].
Proof.
move => sa sb; rewrite / r/ rmin; Ytac h; split => //;try BRo_tac.
case: (rleT_ee sa sb) => //.
Qed.


Lemma rmin_prop2 x y: inc x BRps ->  inc y BRps ->
  inc (rmin x y) BRps.
Proof. by move => sa sb; rewrite / rmin; Ytac h. Qed.

(** pair of converging sequences -------------------- *)

Definition BQpair_aux C :=
   [/\ fgraph C, domain C = Nat,
       forall n, natp n -> inc (Vg C n) (BQ \times BQ),
       forall n, natp n -> P (Vg C n) <q P (Vg C (csucc n))& 
       forall n, natp n -> Q (Vg C (csucc n)) <q Q (Vg C n)].
      
Definition BQpair_aux2a C := 
   forall n, natp n -> P (Vg C n) <q Q (Vg C n).
Definition BQpair_aux2b C := 
   forall n m, natp n -> natp m -> P (Vg C n) <q Q (Vg C m).

Definition BQpair C  :=  BQpair_aux C /\ BQpair_aux2b C.

Definition BQpairL C := 
   Zo BQ (fun x => exists2 n, natp n & x <q P (Vg C n)).
Definition BQpairR C := 
   Zo BQ (fun x => exists2 n, natp n & Q (Vg C n) <q x).

Lemma BQpair_mon C n m:  BQpair_aux C ->
   natp m -> n <c m ->
   P (Vg C n) <q P (Vg C m) /\ Q (Vg C m) <q Q (Vg C n).
Proof.      
move => [pa pb pc pd pe] mN lt1. 
have nN:=(NS_lt_nat lt1 mN).
move/(cleSltP nN): lt1 => mn.
rewrite - (cdiff_pr mn).
move:(NS_diff (csucc n) mN); move: (m -c (csucc n)); apply: Nat_induction.
   rewrite csum0r; fprops; split; fprops.
move => k kN [Hr1 Hr2]. 
have h := (NS_sum (NS_succ nN ) kN).
move: (pd _ h)(pe _ h) => ha hb.
rewrite (csum_nS _ kN); split; BQo_tac.
Qed.


Lemma BQpair_aux2a_equiv C:
   BQpair_aux C -> ( BQpair_aux2a C <-> BQpair_aux2b C).
Proof.
move => cpa; split; last by move => H n nn; apply: H.
move => H n m nN mN.
have qa: n <c csucc (n +c m).
  apply /cltSleP; fprops; apply:csum_M0le; fprops.
have qb: m <c csucc (n +c m).
  rewrite csumC;apply /cltSleP; fprops; apply:csum_M0le; fprops.
have sN :=  (NS_succ (NS_sum nN mN)).
have ha:=(proj1 (BQpair_mon cpa sN qa)).
move:(proj2 (BQpair_mon cpa sN qb)) (H _ sN)  => hb hc.
exact: (qlt_ltT(qlt_ltT ha hc) hb).
Qed.

Lemma BQpair_aux2a_equiv2 C:
  BQpair_aux C -> 
  (BQpair_aux2b C <->disjoint (BQpairL C)(BQpairR C)).
Proof.
move =>H; split.
  move => Ha.
  apply: disjoint_pr => u /Zo_P [uQ [n na nb]]  /Zo_P [_ [m ma mb]].
  by move: (proj2 (qlt_ltT (qlt_ltT nb (Ha _ _ na ma)) mb)).
move => d; apply /(BQpair_aux2a_equiv H) => n nN.
move: H => [pa pb pc pd pe].
move: (pc _ nN) => /setX_P[_ ha hb].
case: (qleT_el hb ha) => // le1.
empty_tac1 (Q (Vg C n)).
   apply /Zo_P; split => //;exists (csucc n); fprops.
   move:(pd _ nN) => h; BQo_tac.
apply /Zo_P; split => //; exists (csucc n); fprops.
Qed.

Lemma BQpair_real C:  BQpair C -> real_dedekind (BQpairR C).
Proof.
move => [Ha Hb].
move:NS0 => ns0.
move: (Ha) => [pa pb pc pd pe].
move:(pc _ NS0) => /setX_P [_ sa sb].
have ra: nonempty (BQpairR C).
   exists (Q (Vg C \0c)) => //;apply:Zo_i => //; exists \1c; fprops.
   by rewrite - succ_zero;apply: pe.
have rb: BQpairR C <> BQ.
   have tx: inc (P (Vg C \0c)) (BQpairL C).
     by apply:Zo_i => //; exists \1c; fprops; rewrite - succ_zero;apply: pd.
   move => eq; move/(BQpair_aux2a_equiv2 Ha): Hb; rewrite eq => di.
   empty_tac1 (P (Vg C \0c)).    
have rc: forall x y, inc x (BQpairR C) -> x <q y -> inc y (BQpairR C).
  move => x y /Zo_P [_ [n na nb]] lxy; move:(proj32_1 lxy) => yq.
  apply:(Zo_i yq); exists n => //; BQo_tac.
split => //;first by apply: Zo_S.
move => x /Zo_P [xq [n na nb]]; move:(pe _ na) => nc.
exists (Q (Vg C n)) => //; apply/Zo_P. 
rewrite -/(ratp _);split; [BQo_tac | exists (csucc n); fprops].
Qed.


Lemma BQpair_irrational C:
  BQpair C ->
  (BQpairL C \cup BQpairR C = BQ) ->
  irrationalp (BQpairR C).
Proof.
move => hab hc.
split; first exact: (BQpair_real hab).
move:hab => [ha hb].
move => x /setC_P [xq xtt].
move: xq; rewrite - {1} hc => /setU2_P; case => // /Zo_P[xq [n na nb]].
exists (P (Vg C n)) => //.
have yq: ratp (P (Vg C n)) by BQo_tac.
move: (ha) => [pa pb pc pd pe].
have hd: inc (P (Vg C n)) (BQpairL C).
  apply: Zo_i => //;exists (csucc n); fprops.
move /(BQpair_aux2a_equiv2 ha):  hb => di.
apply/setC_P;split => // he; empty_tac1 (P (Vg C n)).
Qed.


Lemma BQpair_irrational2  C:
  (BQpairL C \cup BQpairR C = BQ <->
  forall x, ratp x -> exists2 n, natp n &
     (x <q P (Vg C n) \/ Q (Vg C n) <q x)).
Proof.
split => hb.
  move => x; rewrite / ratp - hb => /setU2_P [] /Zo_P [xq [n na nb]].
    by exists n => //; left.
  by exists n => //; right.
set_extens t; first by move/setU2_P => [] /Zo_S.
by move => tq; move/hb: (tq) => [n nN] [] h; 
    apply/setU2_P; [left | right]; apply/Zo_P; split => //; exists n.
Qed.

Lemma BQpair_irrational3 x: irrationalp x -> 
  exists C, [/\  BQpairR C = x,  BQpair C  & BQpairL C \cup BQpairR C = BQ].
Proof.
move => [[pa pb pc pd pe] pf].
pose PR p q := [/\ (P p) <q P q, Q q <q Q p & 
   (Q q -q P q) <q BQhalf  (Q p -q P p)]. 
set E := (BQ -s x) \times x.
have Ha: forall p, inc p E ->  exists q, inc q E /\ PR p q.
  move => p /setX_P [qa qb qd]; move:(pf _ qb) => Hi.
  move/setC_P: qb => [qb qc].
  case: (qleT_ell (pa _ qd) qb) => lt1.
      by case:qc; rewrite - lt1.
    case: qc; apply:(pd _ _ qd lt1).
  move:(BQmiddle_comp lt1); set a := BQmiddle (P p) (Q p).
  move => [lt2 lt3].
  have aq: ratp a by BQo_tac.
  case: (inc_or_not a x) => iax.
    move:Hi => [b ba bb]; exists (J b a); split;first by apply:setXp_i. 
    hnf; saw.
    move/ (BQsum_lt2r (proj31_1 bb) (proj32_1 bb) (QSo aq)): (bb).
    move => / qlt_opp;rewrite (BQoppB (proj32_1 bb) (proj32_1 lt2)).
    rewrite (BQoppB qb (proj32_1 lt2)).
    by rewrite - (BQ_middle_prop2 qb (proj32_1 lt1)).
  move: (pe _ qd) => [b bx lt4]; exists (J a b).
  split;first by apply:setXp_i; [ by apply/setC_P | done].
  move/ (BQsum_lt2r (proj31_1 lt4) (proj32_1 lt4) (QSo aq)): (lt4) => lt5.
  by hnf; saw; rewrite - (BQ_middle_prop1 qb (proj32_1 lt1)).
pose np p:= choose (fun q => inc q E /\ PR p q).
have npp: forall p, inc p E -> (inc (np p) E /\  PR p (np p)).
  move => p pE; apply:(choose_pr (Ha _ pE)).
move:(setC_ne (conj pa pc)) => [a0 a0x].
move:pb =>[b0 b0x].
have qbE: inc (J a0 b0) E by apply:setXp_i.
move: (induction_defined_pr np  (J a0 b0)).
set f := induction_defined np (J a0 b0).
move => [fa fb fc fd].
pose F := Lg  Nat (Vf f).
have Hb: forall n, natp n -> Vg F n =  Vf f n.
   rewrite /F => n nN; rewrite !LgV //.
have Hc1:  Vg F \0c = J a0 b0 by rewrite (Hb _ NS0) fc.
have Hc2:  forall n, natp n -> Vg F (csucc n) = np (Vg F n).
   by move => n nN; rewrite (Hb _ nN) - (fd _ nN) (Hb _ (NS_succ nN)).
have Hd: forall n, natp n -> inc (Vg F n) E /\ PR (Vg F n) (Vg F (csucc n)). 
  apply:Nat_induction.
    rewrite (Hc2 _ NS0) Hc1; split => //; exact (proj2 (npp _ qbE)).
  move => n nN [ha hb]; move:(NS_succ nN) => hc.
  rewrite (Hc2 _ hc)(Hc2 _ nN); move:(proj1 (npp _ ha)) => sa.
  split; [exact | exact:(proj2 (npp _ sa))].
have He:forall n, natp n -> inc (Vg F n) (BQ \times BQ).
  by move => n /Hd [/setX_P [qa /setC_P [qb _] /pa qc] _]; apply/setX_P.
have Hf1:forall n, natp n -> P (Vg F n) <q P (Vg F (csucc n)).
  by move => n /Hd [_ []].
have Hf2:forall n, natp n -> Q (Vg F (csucc n)) <q Q (Vg F n).
  by move => n /Hd [_ []].
have Hg: BQpair_aux F by split => //;rewrite/F; fprops; aw. 
have Hg': BQpair_aux2b F.
  apply/(BQpair_aux2a_equiv Hg) => n nN.
  move:(proj1 (Hd _ nN)) => /setX_P [qa /setC_P [qb qc] qd].
  case:(qleT_ell qb (pa _ qd)) => // ha; case: qc; first by ue.
  apply: (pd _ _ qd ha).
pose delta n := (Q (Vg F n) -q P (Vg F n)).
have deltap: forall n, natp n -> inc (delta n) BQps.
  move => n nN; move: (proj1 (Hd _ nN)) => /setX_P [_ /setC_P [sa sb] sc].
  apply/ qlt0xP; apply/ (qlt_diffP1 sa (pa _ sc)).
  case:(qleT_ell sa (pa _ sc))=> // ha; case: sb;first  by rewrite ha.
  apply: (pd _ _ sc ha).
have Hh: forall n, natp n -> delta n <=q (b0 -q a0) /q (BQ_of_nat (\2c ^c n)).
  move/setC_P: a0x => [aq _]; move:(QS_diff (pa _ b0x) aq) => h.
  rewrite/delta;apply: Nat_induction.
    rewrite Hc1; aw; rewrite cpowx0 /BQ_of_nat -/BZ_one -/BQ_one.
    rewrite (BQdiv_x1 h); apply: (qleR h).
  move => n nN; rewrite (cpow_succ _ nN); set s := _ /q _ => Hrec.
  have ha: ratp (BQ_of_nat (\2c ^c n)) by  apply: QS_of_nat; fprops.
  have hb: ratp (BQ_of_nat \2c) by  apply: (QS_of_nat NS2).
  rewrite (BQprod_cN (NS_pow NS2 nN) NS2) (BQdiv_div2 h ha hb).
  rewrite -/s /BQ_of_nat -/BZ_two -/BQ_two -BQhalf_prop.
  move:(proj2 (Hd _ nN)) => [_ _ hd]. 
  exact (proj1 (qlt_leT  hd(BQhalf_mon Hrec))).
have Hi: forall d, inc d BQps ->  exists2 n, natp n & (delta n <q d).
  move:(deltap _ NS0); rewrite /delta Hc1; aw => lb.
  move => d dp; move:(QpsS_div lb dp) => hb.
  move:(BQ_floorp4 (BQps_sBQ hb)) => [n nN na].
  have ha: BQ_of_nat n <q BQ_of_nat  (\2c ^c n). 
    apply/ qlt_cN; fprops; apply:(cantor (CS_nat nN)).
  move:(qlt_ltT na ha) => nb.
  have hc: inc (BQ_of_nat (\2c ^c n)) BQps.
     move/ qlt0xP:hb => sa; apply/ qlt0xP; BQo_tac.
  move/(BQdiv_lt1P (BQps_sBQ lb) hc dp): nb => hd.
  move:(qlt_ltT (BQhalf_pos1 (deltap _ nN)) (qle_ltT (Hh _ nN) hd)) => he.
  exists (csucc n); first apply: (NS_succ nN).
  move: (proj2 (Hd _ nN)) => [_ _ hf]; BQo_tac.
have Hj: BQpairR F = x.
  set_extens t.
    move /Zo_P => [tq [n nN na]]; move: (proj1 (Hd _ nN)) => /setX_P[_ _ h].
    apply: (pd _ _ h na).
  move => tx; move:(pe _ tx) => [u ux lut]; move:(pa _ tx) (pa _ ux)=> tq uq.
  have dp: inc  (t -q u) BQps.
    by apply/ qlt0xP; apply/ (qlt_diffP1 uq tq).
  move:(Hi _ dp) => [n nN ds]; apply:Zo_i => //; exists n => //.
  move: (proj1 (Hd _ nN)) => /setX_P[ _ /setC_P[sa sb] sc].
  have sd: (P (Vg F n)) <q u.
    case: (qleT_ell sa uq) => // sd; case: sb; [ ue | apply: (pd _ _ ux sd)].
  move:(BQsum_Mltlt sd ds); rewrite /delta.
  by rewrite (BQsum_diff sa (pa _ sc))  (BQsum_diff uq tq).
exists F; split => //.
set_extens t; first by case /setU2_P => /Zo_P [].
move => tq; case: (inc_or_not t x) => tx.
  by apply/setU2_P; right; rewrite Hj.
apply/setU2_P; left.
have /pf [y /setC_P[yq yb] yc ]: inc t (BQ -s x) by apply /setC_P.
have dp: inc (y -q t) BQps.
    by apply/ qlt0xP; apply/ (qlt_diffP1 tq yq).
move:(Hi _ dp) => [n nN ds]; apply:Zo_i => //; exists n => //.
move: (He _ nN) => /setX_P [_ aq bq].
move:(qlt_opp ds);rewrite /delta (BQoppB yq tq) (BQoppB bq aq) => sd.
move: (proj1 (Hd _ nN)) => /setX_P[ _ /setC_P[sa sb] sc].
have se: y <q (Q (Vg F n)).
  case: (qleT_ell yq bq) => // se;case: yb; [ ue |apply: (pd _ _ sc se) ].
by move:(BQsum_Mltlt se sd);rewrite (BQsum_diff yq tq)(BQsum_diff bq aq).
Qed.


Definition BQpair_aux3 C := 
   singletonp (BQ -s ((BQpairL C \cup BQpairR C))).

Lemma BQpair_single3 C:
  BQpair_aux2b C ->
  (BQpair_aux3 C <->
   exists t, [/\ ratp t,
            forall x, x <q t ->  exists2 n, natp n & x <q P (Vg C n) & 
            forall x, t <q x ->  exists2 n, natp n & Q (Vg C n) <q x ]).
Proof.
move => Hb; split.
  move => [t tp]; exists t.
  have aux: forall x, ratp x -> x <> t -> 
       (inc x (BQpairL C) \/ inc x (BQpairR C)).
    move => x xq /set1_P ; rewrite - tp => /setC_P h; ex_middle hh.
    by case h; split => // /setU2_P.
  move: (set1_1 t); rewrite - tp => /setC_P [tq tv]; split => // x lxt.
   case:(aux x (proj31_1 lxt) (proj2 lxt)) => /Zo_P [xq [m ma mb]].
        by exists m.  
    case: tv; apply /setU2_P; right; apply:Zo_i => //; exists m => //; BQo_tac.
   case:(aux x (proj32_1 lxt) (nesym (proj2 lxt))) => /Zo_P [xq [m ma mb]].
    case: tv; apply /setU2_P;left; apply:Zo_i => //; exists m => //; BQo_tac.
   by exists m.  
move => [t [tq ha hb]]; exists t; apply:set1_pr.
   apply/setC_P; split => // /setU2_P; case => /Zo_P [_ [n na nb]].
    move: (hb _ nb) => [m mN hc]; move: (Hb n m na mN) => [nc _]; BQo_tac.
   move: (ha _ nb) => [m mN hc]; move: (Hb _ _ mN na) => [nc _];BQo_tac.
move => z /setC_P [za /setU2_P zu]; case (qleT_ell za tq) => //.
  by move => /ha [n na nb]; case: zu; left; apply:Zo_i => //; exists n.
by move => /hb [n na nb]; case: zu; right; apply:Zo_i => //; exists n.
Qed.

Lemma BQpair_rational C : BQpair C -> BQpair_aux3 C -> 
  exists2 x, ratp x & BQpairR C = BR_of_Q x.
Proof.
move => Hab Hc.
move: Hc => [t tv].
move:(set1_1 t); rewrite - tv; move => /setC_P [tq ta].
exists t => //; set_extens u.
  move => /Zo_P [uq [n nN nv]]; apply /Zo_P; split => //.
  case: (qleT_el tq (proj31_1 nv)) => h; first by BQo_tac.
  by case: ta; apply/setU2_P; right; apply:Zo_i => //; exists n.
move => /Zo_P [uq ltu]. 
case: (inc_or_not u (BQpairL C \cup BQpairR C)) => ha; last first.
  have: inc u (singleton t) by rewrite - tv; apply/setC_P. 
  by move/set1_P => ut; case:(proj2 ltu); rewrite ut.
case/setU2_P: ha => // /Zo_P [_ [n nN nv]].
by case: ta; apply/setU2_P; left; apply:Zo_i => //; exists n => //; BQo_tac.
Qed.


Lemma BQpair_rational2 x: ratp x -> 
   exists C, [/\ BQpairR C = BR_of_Q x, BQpair C & BQpair_aux3 C].
Proof.
move => xq.
pose k n :=  BQ_of_Zinv (BZ_of_nat (csucc n)).
have Hb: forall n, natp n -> k n = BQinv (BQ_of_nat (csucc n)).
  by move => n nN; rewrite /k  - (BQinv_Z ( BQpsS_fromN1 nN)).
have Hc: forall n, natp n -> inc (k n) BQps.
  by move => n nN; rewrite (Hb _ nN); apply: QpsS_inv; apply:  BQpsS_fromN.
have He: forall n, inc n Nat -> k (csucc n) <q k n.
  move => n nN; rewrite (Hb _ nN) (Hb _ (NS_succ nN)).
  apply /(BQinv_mon2 (BQpsS_fromN (NS_succ nN))  (BQpsS_fromN nN)). 
  apply/ qlt_cN; fprops.
set C := Lg Nat (fun n => J (x -q k n) (x +q k n)).
have Hf: BQpair_aux C.
  rewrite /C;split.
  + fprops.
  + by aw.
  + hnf; aw; move => n nN; rewrite LgV//; move: (BQps_sBQ (Hc _ nN)) => h.
    by apply:setXp_i; [apply:QS_diff | apply:QSs ].
  + hnf; aw => n nN;move:(NS_succ nN) => nsN; rewrite !LgV//; aw.
    move:(He _ nN) => / qlt_opp lt1.
   by move /(BQsum_lt2l (proj31_1 lt1)(proj32_1 lt1) xq): (lt1).
  + hnf; aw => n nN;move:(NS_succ nN) => nsN; rewrite !LgV//; aw.
    move:(He _ nN) => lt1. 
    by move /(BQsum_lt2l (proj31_1 lt1)(proj32_1 lt1) xq): (lt1).
have Hd:BQpair_aux2b C.
  apply/(BQpair_aux2a_equiv Hf); rewrite /C; move => n nN; rewrite !LgV//; aw.
  move / qlt0xP: (Hc _ nN) => l1.
  move / qgt0xP: (BQopp_positive1 (Hc _ nN)) => l2.
  move: (qlt_ltT l2 l1) => lt1.
  by move /(BQsum_lt2l (proj31_1 lt1)(proj32_1 lt1) xq): lt1.
have Hg: inc x (BQ -s (BQpairL C \cup BQpairR C)).
  apply/setC_P; split => // /setU2_P; case => /Zo_P [_ [n nN]].
    rewrite /C LgV//; aw => sa.
    move:(BQsum_Mps xq (Hc _ nN)) => se.
    move: (Hc _ nN) => sb; move:(BQps_sBQ sb) => sc.
    move/(BQsum_lt2l xq (proj32_1 sa) sc): sa.
    rewrite (BQsum_diff sc xq) BQsumC; move => [sf _]; BQo_tac.
  rewrite /C LgV//; aw;move:(BQsum_Mps xq (Hc _ nN)) => sa [sb _]; BQo_tac.
have Hh: forall t, x <q t -> inc t (BQpairR C).
  move => z lxz; move:(proj32_1 lxz) => zq; apply/Zo_P; split => //.
  move/(qlt_diffP1 xq zq): lxz  => / qlt0xP /QpsS_inv => h.
  move: (BQ_floorp4 (BQps_sBQ h)) => [n nN na].
  have nb:BQ_of_nat n <q BQ_of_nat (csucc n) by apply/ qlt_cN; fprops.
  move:(qlt_ltT na nb) => /(BQinv_mon2 (BQpsS_fromN nN) h).
  rewrite (BQinv_K (QS_diff zq xq)) => sa. 
  move/(qlt_diffP3 (proj31_1 sa) zq xq): sa; rewrite BQsumC => sb.
  by exists n => //; rewrite /C LgV//; aw; rewrite Hb.
have Hi: BQpairR C = BR_of_Q x.
  set_extens t; last by move => /Zo_P [tq tx]; apply: Hh.
  move/Zo_P => [tq [n na nb]]; apply/Zo_P; split => //.
  move: nb; rewrite /C LgV//;aw.
  move:(BQsum_Mps xq (Hc _ na)) => sa sb; BQo_tac.
exists C; split => //.
exists x; apply: set1_pr => // z /setC_P [zq h].
case: (qleT_ell xq zq) => // lzq; case: h; apply/setU2_P; [right | left ].
   by apply:Hh.
apply/Zo_P; split => //.
move/(qlt_diffP1 zq xq): lzq  => / qlt0xP /QpsS_inv => h.
move: (BQ_floorp4 (BQps_sBQ h)) => [n nN na].
have nb:BQ_of_nat n <q BQ_of_nat (csucc n) by apply/ qlt_cN; fprops.
move:(qlt_ltT na nb) => /(BQinv_mon2 (BQpsS_fromN nN) h).
rewrite (BQinv_K (QS_diff xq zq)) => ha.
move: (proj31_1 ha) => hb.
move/(qlt_diffP3 hb xq zq): ha; rewrite BQsumC => hc.
move/(qlt_diffP3 zq xq hb): hc => hd.
by exists n =>//; rewrite /C LgV//; aw; rewrite Hb.
Qed.

Section BQorder.
Let r := BQ_order.
Let r' := induced_order r (BQ -s1 \0q).

Lemma BQ_order_isomorphisms_spec x:  irrationalp x ->
  exists2 f, order_isomorphism f r' r & Vfs f BQps  = x.
Proof.
move => xi.
move: (BQpair_irrational3 xi) => [C [<- [qa qb] qv]].
move /(BQpair_aux2a_equiv2 qa): qb => di.
move: qa => [q1 q2 q3 q4 q5].
move: (multiple_interpolation_prop3 (f1 :=fun i => Q (Vg C i)) q5 q4 di qv).
by move => [g ga gb]; exists g.
Qed.

Lemma BQ_order_isomorphisms_spec2: exists f, order_isomorphism f r' r.
Proof.
move: (BQ_order_isomorphisms_spec sqrt2_irrational) => [f fa _].
by exists f.
Qed.

End BQorder.

Section Cardinal_real.

Definition CR_inv3n n := BQinv (BQ_of_nat (\3c ^c n)).
Definition CR_next_term f n := (BQ_of_nat (Vf f n)) *q (CR_inv3n n).
Definition CR_partial_sum f n := qsum (CR_next_term f) (csucc n).
Definition CR_set := functions Nat \2c.

Lemma CR_prop0 n: natp n -> inc (CR_inv3n n) BQps.
Proof.
move => nN; apply: QpsS_inv; apply: QpsS_of_nat.  
  apply: NS_pow => //; apply: NS3.
apply: cpow_nz; apply: card3_nz.
Qed.

Lemma CR_prop1 n: natp n -> ratp (CR_inv3n n).
Proof. by  move => /CR_prop0 /BQps_sBQ. Qed.

Definition CR_limit f := Zo BQ (fun z => exists2 n, natp n & 
    CR_partial_sum f n +q (CR_inv3n n) <q z).


Section Aux.
Variable f:Set.
Hypothesis fI: inc f CR_set. 


Lemma CR_prop2 n: natp n ->
   CR_next_term f n = \0q \/ CR_next_term f n = (CR_inv3n n).
Proof.
move => nN; move /functionsP:fI => [ff sf tf].
have ns: inc n (source f) by ue.
move:(CR_prop1 nN) => tq.
move:(Vf_target ff ns); rewrite /CR_next_term  tf => /set2_P; case => ->.
  by left; rewrite BQprod_0l.  
by right;rewrite BQprod_1l.
Qed.

Lemma CR_prop3  n: natp n -> inc (CR_next_term f n) BQp.
Proof.
move => nN; case: (CR_prop2 nN) => ->; first by apply: QpS0.
apply:(BQps_sBQp (CR_prop0 nN)).
Qed.


Lemma CR_prop4 n: natp n ->  inc (qsum (CR_next_term f) n) BQp.
Proof.
move: n; apply: Nat_induction; first by rewrite qsum0; apply: QpS0.
move => n nN hr; rewrite (qsum_rec _ nN); apply: QpS_sum hr.
by apply: CR_prop3.  
Qed.

Lemma CR_prop5 n : natp n ->
  CR_partial_sum f n <=q  CR_partial_sum f (csucc n).
Proof.
move => nN; rewrite /CR_partial_sum  (qsum_rec _ (NS_succ nN)).
have pa:= (CR_prop3 (NS_succ nN)).
have pb:=(BQp_sBQ (CR_prop4 (NS_succ nN))).
rewrite BQsumC; apply:(BQsum_Mp pb pa). 
Qed.

Lemma CR_prop6 n : natp n ->
  CR_partial_sum f (csucc n) <=q  CR_partial_sum f n +q (CR_inv3n (csucc n)).
Proof.
move =>  nN; rewrite /CR_partial_sum  (qsum_rec _ (NS_succ nN)).
have ha:=  (CR_prop0 (NS_succ nN)).
have hb:=  (CR_prop3 (NS_succ nN)).
have hc:= (proj31 (CR_prop5  nN)).
rewrite BQsumC; apply/(BQsum_le2l (BQp_sBQ hb) (BQps_sBQ ha) hc).
case: (CR_prop2 (NS_succ nN)) => ->. 
  apply/ qle0xP; apply: (BQps_sBQp ha).
apply: (qleR  (BQps_sBQ ha)).
Qed.

Lemma CR_prop00 n: natp n ->  (CR_inv3n n) = \3q *q (CR_inv3n (csucc n)).
Proof.
move => nN.
rewrite/CR_inv3n (cpow_succ _ nN) (BQprod_cN (NS_pow NS3 nN) NS3).
have Hu: ratp (BQ_of_nat (\3c ^c n)).
    apply:QS_of_nat; apply: (NS_pow NS3 nN).
rewrite(BQprod_inv Hu QS3);symmetry; apply: (BQprod_div QS3 (CR_prop1 nN)).
move /pr1_def => /pr1_def; exact: card3_nz.
Qed.

(* dans ssetq1 *)
Lemma BQ_double_plus x:ratp x -> BQdouble x +q x = \3q *q x.
Proof.
move => rx; rewrite -{2} (BQprod_1l rx) /BQdouble - (BQprodDl rx QS2  QS1).
by rewrite (BQsum_cN NS2 NS1) - (Nsucc_rw NS2).
Qed.


Lemma CR_prop7 n k (h := fun i => CR_partial_sum f i  +q BQhalf (CR_inv3n i)):
   natp n -> natp k -> (h (n+c k) <=q h n).
Proof.
move => nN; move: k; apply:Nat_induction.
  rewrite (csum0r (CS_nat nN)); apply:qleR; apply: QSs.
    exact:(BQp_sBQ (CR_prop4 (NS_succ nN))).
  apply:(QS_half (CR_prop1 nN)).
move => k kN hr.
apply: qleT hr.
rewrite (csum_nS _ kN) /h.
have sN:=  (NS_sum nN kN).
move: (CR_prop6 sN) => hh.
have ns3:= NS3.
have nsp:= NS_pow ns3 sN.
have Ha:= (CR_prop1 (NS_succ sN)).
have Hb:= (QS_half Ha).
have <-: (CR_inv3n (csucc (n +c k)) +q BQhalf (CR_inv3n (csucc (n +c k))))
         = BQhalf (CR_inv3n (n +c k)).
  rewrite (CR_prop00 sN) -{1}(BQhalf_double Ha).
  by rewrite /BQhalf -(BQprodDl QSh2 (QSdouble Ha) Ha) BQ_double_plus.
move/(BQsum_le2r (proj31 hh) (proj32 hh) Hb):hh.
by rewrite (BQsumA (proj31  (CR_prop5 sN)) Ha Hb).
Qed.


Lemma CR_prop8 n k: natp n -> natp k ->
  CR_partial_sum f k <=q CR_partial_sum f n +q  (CR_inv3n n).
Proof.
move => nN kN.
case: (NleT_ee kN nN) => lkn.
  have Ha: CR_partial_sum f n <=q CR_partial_sum f n +q CR_inv3n n.
    apply:(BQsum_Mp (proj31 (CR_prop5 nN)) (BQps_sBQp (CR_prop0 nN))).
  apply:(qleT _ Ha).
  rewrite -(cdiff_pr lkn); move:(NS_diff k nN); move:(_ -c _).
  apply: Nat_induction.
    by rewrite (csum0r (CS_nat kN)); exact:(qleR (proj31 (CR_prop5 kN))) => xQ.
  move => m mN Hr; apply: (qleT Hr);rewrite (csum_nS _ mN).
  exact:(CR_prop5 (NS_sum kN mN)).
move:(cdiff_pr lkn)(NS_diff n kN); set m := (_ -c _) => kv mN.
move: (CR_prop7 nN mN); rewrite kv => hb.
have ha: (CR_partial_sum f k) <=q CR_partial_sum f k +q BQhalf (CR_inv3n k).
   apply:(BQsum_Mp (proj31 (CR_prop5 kN))).
   exact: (BQps_sBQp (BQhalf_pos  (CR_prop0 kN))).
apply: (qleT (qleT ha hb)).
have qa:= (CR_prop0 nN); have qb := (BQps_sBQ qa).
apply /(BQsum_le2l (QS_half qb) qb (proj31 (CR_prop5 nN))).
exact:(proj1 (BQhalf_pos1 qa)).
Qed.

Lemma CR_prop9 n: natp n ->
  inc (CR_partial_sum f n +q (CR_inv3n n)) (CR_limit f).
Proof.
move => nN.
move:(CR_prop6 nN) => eq1.
move:(CR_prop5 nN) => [xq yq _].
move: (CR_prop1 nN) (CR_prop1 (NS_succ nN)) => cc cc1.
move: (QSdouble cc1) => cc2.
apply: (Zo_i (QSs xq cc)); exists (csucc n); first by apply: (NS_succ nN).
move/ (BQsum_le2r yq (proj32 eq1) cc1): eq1 => eq2; apply:(qle_ltT eq2).
rewrite - (BQsumA xq cc1 cc1) (BQdouble_p cc1)  (CR_prop00 nN).
rewrite - (BQ_double_plus cc1) (BQsumA xq cc2 cc1).
apply:(BQsum_Mps (QSs xq cc2)) (CR_prop0 (NS_succ nN)).
Qed.

Lemma CR_prop10 k: natp k -> ~inc (CR_partial_sum f k) (CR_limit f).
Proof.
move => kN /Zo_P [tq [n nN ltn] ].
by case: (qle_ltT  (CR_prop8 nN kN) ltn).
Qed.

Lemma CR_prop11 : realp (CR_limit f).
Proof.
apply/BR_P;split.
- apply: Zo_S.
- move:(CR_prop9 NS0) => xx; ex_tac.  
- move => h; move: QS0; rewrite / ratp - h => /Zo_P [_ [n nN / qgt0xP h2]].
  case: (BQ_di_neg_pos h2).
  exact:(QpS_sum (CR_prop4 (NS_succ nN)) (BQps_sBQp (CR_prop0 nN))).
- move => x y /Zo_P [ha [n hb hc]] lxy; apply /Zo_P; split.
    exact (proj32_1 lxy).
  by exists n => //; apply:(qlt_ltT hc lxy).
move => x /Zo_P [ha [n hb hc]].
move:(BQmiddle_comp hc); set y := BQmiddle _ _; move => [qa qb].
by exists y => //; apply/Zo_P; split; [ exact: (proj31_1 qb) |  exists n].
Qed.


End Aux.


    
Lemma CR_prop12: injection (Lf CR_limit CR_set BR). 
Proof.
apply: lf_injective; first by apply:CR_prop11. 
move => u v uI vI sm; ex_middle nuv.
set E := Zo Nat (fun i => (Vf u i <> Vf v i)).
case:(emptyset_dichot E) => ee.
  move/functionsP:uI=> [fu su tu]; move/functionsP:vI => [fv sv tv].
  apply :(function_exten fu fv); [ ue |  ue | ].
  rewrite su;move => n nN /=; ex_middle bad.
  empty_tac1 n; apply/Zo_P; split => //.
have sEN: sub E Nat by apply: Zo_S.
move:(inf_Nat sEN ee) ; set k := intersection E; move => [kq kp].
have kN := sEN _ kq.
have lkp: forall i, i <c k -> Vf u i = Vf v i.
  move => i lik; ex_middle bad; case: (cltNge lik); apply: kp; apply:Zo_i => //.
  apply: (NS_lt_nat lik kN).
have lkk: Vf u k <> Vf v k by case /Zo_P: kq.
have:  CR_partial_sum u k =  CR_partial_sum v k +q (CR_inv3n k)
  \/  CR_partial_sum v k =  CR_partial_sum u k +q (CR_inv3n k).
  rewrite /CR_partial_sum (qsum_rec _ kN) (qsum_rec _ kN).
  set x := qsum _ _; set y := qsum _ _.
  have <-: x = y.
  have aux: forall n, natp n -> n <=c k ->
                  qsum (CR_next_term u) n = qsum (CR_next_term v) n.
     apply:Nat_induction; first by rewrite !qsum0.
     move => n nN Hrec snk. rewrite (qsum_rec _ nN)  (qsum_rec _ nN).
     move/(cleSltP nN): snk => lnk.
     by rewrite (Hrec (proj1 lnk)); rewrite /CR_next_term (lkp _ lnk).
    exact:(aux k kN (cleR (CS_nat kN))).
  have xq: ratp x by exact:(BQp_sBQ(CR_prop4 uI kN)).
  move/functionsP:uI => [fu su tu];move/functionsP:vI => [fv sv tv].
  rewrite /CR_next_term; set w := CR_inv3n k.
  have uk2: (Vf u k) = \0c \/ (Vf u k) = \1c.
    by apply/set2_P; rewrite  - [doubleton _ _]/ \2c; Wtac; rewrite su.
  have vk2: (Vf v k) = \0c \/ (Vf v k) = \1c.
    by apply/set2_P; rewrite  - [doubleton _ _]/ \2c; Wtac; rewrite sv.
  have wq: ratp w. apply: (CR_prop1 kN).
  move:lkk;case: uk2 => uk; rewrite uk;case: vk2 => vk; rewrite vk.
  + by case.
  + by right
         ;rewrite (BQprod_0l wq) (BQprod_1l wq)(BQsum_0l xq) BQsumC. 
  + by left;rewrite (BQprod_0l wq) (BQprod_1l wq)(BQsum_0l xq) BQsumC.
  + by case.
case => H.
  by case:(CR_prop10 uI kN);move: (CR_prop9 vI kN); rewrite - H - sm. 
by case:(CR_prop10 vI kN); move: (CR_prop9 uI kN); rewrite - H - sm.
Qed.

Lemma card_R: cardinal BR = \2c ^c aleph0.
Proof.
apply: cleA.
  have: sub BR (powerset BQ) by move => j /Zo_P [].
  by move/sub_smaller; rewrite  card_setP - cpowcr cardinal_Q.
by move: (inj_source_smaller CR_prop12); aw.
Qed.


End Cardinal_real.
  
(** Cauchy sequences *)

Definition BQ_seq x := [/\ fgraph x, domain x = Nat & sub (range x) BQ].
Definition BR_seq x := [/\ fgraph x, domain x = Nat & sub (range x) BR].


Definition CauchyQ x := BQ_seq x /\
      forall e, inc e BQps -> exists2 N, natp N &
         forall n m, natp n -> natp m -> N <=c n -> N <=c m ->
            BQabs ((Vg x n) -q (Vg x m)) <q e.

Definition CauchyR x := BR_seq x /\
      forall e, inc e BQps -> exists2 N, natp N &
         forall n m, natp n -> natp m -> N <=c n -> N <=c m ->
            BRabs ((Vg x n) -r (Vg x m)) <r (BR_of_Q e).


Definition limitQ x v:= 
   forall e, inc e BQps -> exists2 N, natp N &
   forall n, natp n ->  N <=c n -> BQabs ((Vg x n) -q v) <q e.

Definition limitR x v:= 
   forall e, inc e BQps -> exists2 N, natp N &
   forall n, natp n ->  N <=c n -> BRabs ((Vg x n) -r v) <r (BR_of_Q e).

Lemma BRcompare_zero' e: inc e BQps -> 
   exists2 e', inc e' BRps & e' <r (BR_of_Q e).
Proof.
move => ep.
move:(BQhalf_pos1 ep)(BQhalf_pos ep).
set e1 :=  BQhalf e => sa sb.
move /(rlt_cQ (proj31_1 sa) (proj32_1 sa)): sa => sa'.
move: (RpsS_of_Q sb) => sc; ex_tac.
Qed.

Lemma BR_seq_prop s n: BR_seq s -> natp n -> realp (Vg s n).
Proof.
by move => [sa sb sc] nn;apply sc; apply /(range_gP sa); rewrite sb; exists n.
Qed.

Lemma BQ_seq_prop s n: BQ_seq s -> natp n -> ratp (Vg s n).
Proof.
by move => [sa sb sc] nn;apply sc; apply /(range_gP sa); rewrite sb; exists n.
Qed.


Lemma CauchyR_alt x: CauchyR x <->
   (BR_seq x /\  forall e, inc e BRps -> exists2 N, natp N &
         forall n m, natp n -> natp m -> N <=c n -> N <=c m ->
            BRabs ((Vg x n) -r (Vg x m)) <r e).
Proof.
split; move => [pa pb]; split => //.
  move => e /BRcompare_zero [e' ra rb].
  move: (pb _ ra) => [N NN h]; exists N => // n m nN mN na nb.
  move:(h _ _ nN mN na nb) => lt1; BRo_tac.
move => e /BRcompare_zero' [e' ra rb].
move: (pb _ ra) => [N NN h]; exists N => // n m nN mN na nb.
move:(h _ _ nN mN na nb) => lt1; BRo_tac.
Qed.

Lemma limitR_alt x v : (limitR x v) <->
  forall e, inc e BRps -> exists2 N, natp N &
  forall n, natp n ->  N <=c n -> BRabs ((Vg x n) -r v) <r e.
Proof.
split.
  move => H e /BRcompare_zero [e' ra rb].
  move:(H _ ra) => [N nN Hn]; exists N=> //n na nb; move:(Hn n na nb).
  move => lt; BRo_tac.
move => H e /BRcompare_zero' [e' ra rb].
move:(H _ ra) => [N nN Hn]; exists N=> //n na nb; move:(Hn n na nb).
move => lt; BRo_tac.
Qed.


Lemma limitQ_unique x v1 v2: BQ_seq x -> ratp v1 -> ratp v2 ->
   limitQ x v1 -> limitQ x v2 -> v1 = v2.
Proof.
move => pa v1q v2q ha hb.
ex_middle ne.
have dq:= (QS_diff v2q v1q).
set d := BQhalf(BQabs (v2 -q v1)).
have dp: inc d BQps.
   apply:BQhalf_pos; apply/BQps_iP; split; first by apply:QpSa.
   by apply /(BQabs0_bis dq) =>/(BQdiff_xx_rw v2q v1q) eq1; case:ne.
move: (ha _ dp) (hb _ dp)=> [n1 n1N na][n2 n2N nb].
move:(cmax_p1 (CS_nat n1N)(CS_nat n2N)); set m := cmax n1 n2; move => [ma mb].
have mN: natp m by apply:Gmax_E.
move:(na _ mN ma)(nb _ mN mb) => hc hd.
have he: inc (Vg x m) BQ by apply: (BQ_seq_prop pa mN).
move: (qle_triangular (QS_diff he v1q) (QS_diff v2q he)).
rewrite - (BQdiff_sum_comm he (QS_diff v2q he) v1q) (BQsum_diff he v2q).
move:(BQsum_Mltlt hc hd);rewrite (BQdouble_half1 (QSa dq)).
rewrite (BQabs_diff v2q he) => sa sb; BQo_tac.
Qed.


Lemma limitR_unique x v1 v2: BR_seq x -> realp v1 -> realp v2 ->
   limitR x v1 -> limitR x v2 -> v1 = v2.
Proof.
move => pa v1q v2q ha hb.
ex_middle ne.
have dq:= (RS_diff v2q v1q).
set d := BRhalf (BRabs (v2 -r v1)).
have dp: inc d BRps.  
  by apply:BRhalf_pos; apply:RpsSa => //  /(BRdiff_xx_rw v2q v1q) eq1; case:ne.
move/limitR_alt: ha => ha1.
move/limitR_alt: hb => hb1.
move: (ha1 _ dp) (hb1 _ dp)=> [n1 n1N na][n2 n2N nb].
move:(cmax_p1 (CS_nat n1N)(CS_nat n2N)); set m := cmax n1 n2; move => [ma mb].
have mN: natp m by apply:Gmax_E.
move:(na _ mN ma)(nb _ mN mb) => hc hd.
have he: realp (Vg x m) by apply: (BR_seq_prop pa mN).
move: (rle_triangular (RS_diff he v1q) (RS_diff v2q he)).
rewrite - (BRdiff_sum_comm he (RS_diff v2q he) v1q) (BRsum_diff he v2q).
move:(BRsum_Mltlt hc hd);rewrite (BRdouble_half1 (RSa dq)).
rewrite (BRabs_diff v2q he) => sa sb; BRo_tac.
Qed.

Lemma CauchyQ_when_limit x: BQ_seq x -> (exists2 y, ratp y & limitQ x y) ->
   CauchyQ x.
Proof.
move => ha [y yq hb]; split => // e ep.
move:(BQhalf_pos ep) => hep.
move:(hb _ hep) => [N NN etc]; exists N => // n m nN mN na nb.
move: (etc n nN na)(etc m mN nb) => sa sb.
move:(BQsum_Mltlt sa sb); rewrite (BQdouble_half1 (BQps_sBQ ep))=> sc.
have xnq: ratp (Vg x n) by apply: BQ_seq_prop. 
have xmq: ratp (Vg x m) by apply: BQ_seq_prop. 
move: (qle_triangular (QS_diff xnq yq) (QS_diff yq xmq)).
rewrite (BQsumA  (QS_diff xnq yq) yq (QSo xmq))  (BQsum_diff1 yq xnq).
rewrite (BQabs_diff yq xmq) => sd; BQo_tac.
Qed.


Lemma CauchyR_when_limit x: BR_seq x -> (exists2 y, realp y & limitR x y) ->
   CauchyR x.
Proof.
move => ha [y yq hb]; split => // e ep.
have hep:=(BQhalf_pos ep).
have heq:=(BQps_sBQ hep).
move:(hb _ hep) => [N NN etc]; exists N => // n m nN mN na nb.
move: (etc n nN na)(etc m mN nb) => sa sb.
move:(BRsum_Mltlt sa sb). rewrite (BRsum_cQ heq heq).
rewrite (BQdouble_half1 (BQps_sBQ ep))=> sc.
have xnq: realp (Vg x n) by apply: BR_seq_prop. 
have xmq: realp (Vg x m) by apply:BR_seq_prop.
move: (rle_triangular (RS_diff xnq yq) (RS_diff yq xmq)).
rewrite (BRsumA  (RS_diff xnq yq) yq (RSo xmq))  (BRsum_diff1 yq xnq).
rewrite (BRabs_diff yq xmq) => sd; BRo_tac.
Qed.

Lemma BR_seq_prop1 f: (forall n, natp n -> realp (f n)) ->
   BR_seq (Lg Nat f).
Proof.
move => h.
have sa:fgraph (Lg Nat f) by fprops.
have sb: (domain (Lg Nat f)) = Nat by aw.
by split => // t /(range_gP sa); rewrite sb; move => [n na ->]; rewrite LgV//; apply: h.
Qed.


Definition BR_seq_of_Q s :=  Lg Nat (fun n => (BR_of_Q (Vg s n))).

Lemma BR_seq_of_Q_seq s: BQ_seq s -> BR_seq (BR_seq_of_Q s).
Proof.
by move => sa;apply:BR_seq_prop1 => n nN; apply:RS_of_Q;apply: BQ_seq_prop.
Qed.


Lemma BR_seq_of_Q_cauchy s: CauchyQ s -> CauchyR (BR_seq_of_Q s).
Proof.
move => [su sd].
move:(BR_seq_of_Q_seq su) => sa'.
split => // e ep; move:(sd _ ep) => [N nN etc]; exists N => //n m na nb nc nd. 
rewrite /BR_seq_of_Q; move:(etc _ _ na nb nc nd); rewrite !LgV//.
have ha: ratp (Vg s n) by apply: BQ_seq_prop. 
have hb: ratp (Vg s m) by apply: BQ_seq_prop. 
rewrite(BRdiff_cQ ha hb) (BRabs_cQ (QS_diff ha hb)) => h.
by move/(rlt_cQ (proj31_1 h)  (proj32_1 h)):h.
Qed.


Lemma BR_limit_of_rat x: realp x ->
   exists2 s, CauchyQ s & limitR (BR_seq_of_Q s) x.
Proof.
move => xr.
have[C ca [[cb cc cd ce cf] cg]]: exists2 C, BQpairR C = x & BQpair C.
  case: (BR_rational_dichot xr) => rx.
    move: (BR_of_Q_prop2 rx) => [y ry yv].
    move:(BQpair_rational2 ry) => [c [ca cb _]]; exists c => //; ue.
  move:(BQpair_irrational3 rx) => [c [ca cb _]]; exists c => //; ue.
set s := Lg Nat (fun n => Q (Vg C n)).
have fgs: fgraph s by rewrite /s; fprops.
have  ds: domain s = Nat by rewrite /s; aw.
have Ha: forall n, natp n -> ratp (Q (Vg C n)).
  by  move => n /cd /setX_P[_ _].
have Hb: forall n, inc n Nat -> ratp (Vg s n).
  by rewrite /s => n nn; rewrite LgV//; apply: Ha.
have ss: BQ_seq s.
  by split => // t /(range_gP fgs); rewrite ds; move => [y ua ->]; apply: Hb.
have Cdec: forall n m, natp n -> natp m -> n <=c m ->
   (Q (Vg C m)) <=q (Q (Vg C n)).
   move => n m nn mn lemn.
   rewrite - (cdiff_pr lemn); move: (NS_diff n mn).
   move: (m -c n); apply: Nat_induction.
      rewrite (csum0r (CS_nat nn)); apply:qleR; fprops.
   move => k kN Hrec; rewrite (csum_nS _ kN).
   exact:(qleT (proj1 (cf _ (NS_sum nn kN))) Hrec).
have Hc: forall n, natp n -> inc (Q (Vg C n)) x.
  move => n nn; rewrite - ca; apply/Zo_P; split; first by apply: Ha.
    exists (csucc n);fprops.
have cs: CauchyQ s.
  split => // e ep; move:(BRi_lowbound xr ep) => [y yx Hy].
  move: yx; rewrite - ca => /Zo_P[yq[n na nb]]; exists n => //.
  move => n1 n2 n1n n2n nc nd.
  wlog n1n2: n1 n2 n1n n2n nc nd / n1 <=c n2.
    move => H; case: (NleT_ee n1n n2n) => ele; first by apply:H.
    rewrite BQabs_diff; fprops.
  have hc: inc (Q (Vg C n1) -q Q (Vg C n2)) BQp.
     move: (Cdec _ _ n1n n2n n1n2) => sa.
     by move /(qle_diffP1 (proj31 sa) (proj32 sa)) : sa => / qle0xP.
  rewrite /s ! LgV// (BQabs_pos hc).
  move: (Hy _ (Hc _ n2n)) => /(BQdiff_lt1P yq (BQps_sBQ ep) (Ha _ n2n)) => sa.
  move: (qle_ltT (Cdec _ _ na n1n nc) nb) => sb.
  move/(BQsum_lt2r (proj31_1 sb)(proj32_1 sb) (QSo (Ha _ n2n))): sb.
  move => sc; BQo_tac.
exists s => // e ep; move:(BRi_lowbound xr ep) => [y yx Hy].
move: yx; rewrite - {1} ca => /Zo_P[yq[n na nb]]; exists n => //.
move: (BQps_sBQ ep) => eq.
have ha: BR_of_Q  (y -q e)  <=r x.
   by apply:(BR_le_aux3 xr (QS_diff yq eq)) => /Hy [_].
move => m mN nm. 
move: (qle_ltT (Cdec _ _ na mN nm) nb) => sb.
move/(BQsum_lt2r (proj31_1 sb)(proj32_1 sb) (QSo eq)): sb => sc.
move /(rlt_cQ (proj31_1 sc)(proj32_1 sc)): sc => sd.
rewrite /BR_seq_of_Q /s !LgV//.
have sa: (inc (BR_of_Q (Q (Vg C m)) -r x) BRp).
  move: (proj1 (BR_le_aux2 xr (Hc _ mN))) => sa.
  by apply/ rle0xP; apply/ (rle_diffP1 (proj31 sa) (proj32 sa)).
rewrite /BRabs (Y_true sa).
apply / (BRdiff_lt1P (RS_of_Q  (Ha _ mN)) xr (RS_of_Q (BQps_sBQ ep))).
rewrite (BRdiff_cQ (Ha _ mN) (BQps_sBQ ep)); BRo_tac.
Qed.

Definition similar_seq x y := 
 (forall e, inc e BQps -> exists2 N, natp N &
      forall n, natp n -> N <=c n -> 
            BRabs ((Vg x n) -r (Vg y n))  <r (BR_of_Q e)).

Lemma similar_seq_sym x y: BR_seq x -> BR_seq y -> similar_seq x y ->  
   similar_seq y x.
Proof.
move => sx sy h e ep. 
move: (h e ep) => [n na nb]; exists n => // m ma mb.
have ha: realp (Vg y m)  by apply:BR_seq_prop.
have hb: realp (Vg x m)  by apply:BR_seq_prop.
by rewrite (BRabs_diff ha hb); apply: nb.
Qed.

Lemma limitR_same x y z:  BR_seq x  -> BR_seq y -> realp z ->
   similar_seq x y  ->  limitR x z ->  limitR y z.
Proof.
move=> sx sy zr H l1 e ep.
move: (BQhalf_pos ep)(QS_half (BQps_sBQ ep)) => hep hq.
move: (H _ hep)  (l1 _ hep) => [n na nb]  [m ma mb].
move:(cmax_p1 (CS_nat na)(CS_nat ma)); set k := cmax n m; move => [ka kb].
have kN: natp k by apply:Gmax_E.
exists k => // q qn kq.
move:(nb _ qn (cleT ka kq))(mb _ qn (cleT kb kq)) => hc hd.
have: realp (Vg x q) by apply:BR_seq_prop.
have: realp (Vg y q) by apply: BR_seq_prop.
move => ha hb; move:(rle_triangular (RS_diff ha hb) (RS_diff hb zr)).
rewrite (BRsumA (RS_diff ha hb) hb (RSo zr))(BRsum_diff1 hb ha).
move: (BRsum_Mltlt hc hd); rewrite (BRabs_diff hb ha).
rewrite (BRsum_cQ hq hq) (BQdouble_half1  (BQps_sBQ ep)) => sa sb.
BRo_tac.
Qed.

Lemma BQ_denseR x e: realp x -> inc e BQps -> 
   exists2 y, ratp y & BRabs (x -r (BR_of_Q y)) <r (BR_of_Q e).
Proof.
move => xr ep.
case: (BR_rational_dichot xr) => rx.
   move:(BR_of_Q_prop2 rx) => [y yq yv]; exists y => //; rewrite -yv.
   by rewrite (BRdiff_xx xr) BRabs_0; apply / rlt0xP; apply: RpsS_of_Q.
move: (proj2 rx) => sa.
move:(BRi_lowbound xr ep) => [y yx Hy].
move: (BRi_sQ xr yx) (BQps_sBQ ep) => yq eq.
move:(BR_le_aux2 xr yx) =>/ (rlt_diffP1  xr (RS_of_Q yq)) / rlt0xP => h.
exists y => //.
have ->: BRabs (x -r BR_of_Q y) =  BR_of_Q y -r x.
  by rewrite (BRabs_diff xr (RS_of_Q yq)) /BRabs (Y_true (BRps_sBRp h)).
apply /(BRdiff_lt1P (RS_of_Q yq) xr (RS_of_Q eq)).
rewrite (BRdiff_cQ yq eq); split.
   by apply: (BR_le_aux3 xr (QS_diff yq eq)) => /Hy [_].
move => e2.
by move:(proj2 (BR_of_Q_prop1 (QS_diff yq eq))); rewrite e2; case.
Qed.

Lemma BQ_denseR2 x: realp x ->
  (exists2 y, ratp y & x <r (BR_of_Q y))
  /\ (exists2 y, ratp y & (BR_of_Q y) <r x).
Proof.
move => xr; move:(BQ_denseR xr QpsS1) =>[y yq].
move /(BRabs_prop4 xr (RS_of_Q yq) RS1) =>[].
rewrite (BRdiff_cQ yq QS1) (BRsum_cQ yq QS1) => sa sb.
split; first by  exists (y +q \1q) => //;exact:(QSs yq QS1).  
exists (y -q \1q) => //;exact:(QS_diff yq QS1).
Qed.

Lemma limitR_same2 x: CauchyR x -> 
   exists2 y, CauchyQ y & similar_seq x (BR_seq_of_Q y).
Proof.
move => cx.
pose k n := (BQinv (BQ_of_nat (csucc n))). 
have Ha: forall n, natp n -> inc (k n) BQps.
  by move => n nN; apply: QpsS_inv; apply: BQpsS_fromN.
pose p x n y := ratp y /\  BRabs (x -r (BR_of_Q y)) <r (BR_of_Q (k n)).
pose the_y x n := choose (p x n).
have the_yp: forall x n, realp x -> natp n -> p x n (the_y x n).
    move => z n xr nn; move:(Ha _ nn) => kp;move:(BQ_denseR xr kp) =>[y ya yb].
    have Hb:exists y, p z n y by  exists y; split.
    apply:(choose_pr Hb).
set y := Lg Nat (fun n => the_y (Vg x n) n).
have fgy: fgraph y by rewrite /y; fprops.
have dy: domain y = Nat by rewrite /y; aw.
move: cx => [[pa pb pc] pd].
have sy: BQ_seq y. 
   split => // t /(range_gP fgy) [n]; rewrite dy => na ->.
   have zr: realp (Vg x n) by apply:BR_seq_prop.
   rewrite /y LgV//; exact :(proj1 (the_yp _ _ zr na)).
have Hb: forall n m, natp n -> natp m -> n <=c m ->
    (k m) <=q  BQinv (BQ_of_nat (csucc n)).
  move => n m nN mN h.
  apply/(BQinv_mon1 (BQpsS_fromN mN)  (BQpsS_fromN nN)). 
  by apply/(qle_cN (NS_succ nN) ((NS_succ mN))); apply:cleSS.
have cy: CauchyQ y.
  split => // e ep.
  move: (BQhalf_pos ep) => e1p; move:(BQhalf_pos e1p) => e2p.
  move:(pd _ e1p) => [n1 n1N Hc].
  move:(BQpsS_fromN_large e2p) => [n2 n2N Hd].
  move:(cmax_p1 (CS_nat n1N)(CS_nat n2N)); set N := cmax _ _ ; move => [ka kb].
  have NN: natp N by apply:Gmax_E.
  exists N => // n m nN mN le1 le2.
  have xnr: realp (Vg x n) by apply:  BR_seq_prop.
  have xmr: realp (Vg x m) by apply:  BR_seq_prop.
  move: (the_yp _ _ xnr nN)(the_yp _ _ xmr mN) =>[ua ub][va vb].
  move: (qle_ltT (Hb n2 n n2N nN (cleT kb le1)) Hd) => lt1.
  move: (qle_ltT (Hb n2 m n2N mN (cleT kb le2)) Hd) => lt2.
  move /(rlt_cQ (proj31_1 lt1) (proj32_1 lt1)): lt1 => lt3.
  move /(rlt_cQ (proj31_1 lt2) (proj32_1 lt2)): lt2 => lt4.
  move:(rlt_ltT ub lt3) => lt5.
  move:(rlt_ltT vb lt4) => lt6.
  move: (Hc n m nN mN (cleT ka le1) (cleT ka le2)) => lt7.
  move: (BRsum_Mltlt (BRsum_Mltlt lt7 lt5) lt6).
  move:(BQps_sBQ e2p) (BQps_sBQ e1p) => e2q e1q. 
  move: (RS_of_Q (BQps_sBQ e1p)) (RS_of_Q e2q) => qa qb.
  move: (RS_of_Q ua) (RS_of_Q va) => ua' va'.
  rewrite (BRabs_diff xnr ua').
  move: (RS_diff xnr xmr) (RS_diff ua' xnr)(RS_diff xmr va') => ur vr wr.
  rewrite - (BRsumA qa qb qb) (BRsum_cQ e2q e2q) (BQdouble_half1 e1q);
  rewrite  (BRsum_cQ e1q e1q) (BQdouble_half1 (BQps_sBQ ep)) => la.
  move:(rle_triangular ur vr) => lb.
  move/(BRsum_le2r (proj31 lb) (proj32 lb) (RSa wr)):lb => lc.
  move:(rle_ltT (rleT (rle_triangular (RSs ur vr) wr) lc) la).
  rewrite (BRsumC (Vg x n -r Vg x m)) (BRsumA (RS_diff ua' xnr) xnr (RSo xmr)).
  rewrite (BRsum_diff1 xnr ua') (BRsumA (RS_diff ua' xmr) xmr (RSo va')).
  rewrite (BRsum_diff1 xmr ua').
  rewrite -/(_ -r _ ) (BRdiff_cQ ua va) (BRabs_cQ (QS_diff  ua va)).
  move / (rlt_cQ (QSa (QS_diff ua va)) (BQps_sBQ ep)).
  rewrite /y !LgV//.
have sxy: similar_seq x (BR_seq_of_Q y).
  move => e ep; move: (BQpsS_fromN_large ep) => [n na nb].
  exists n => // m mN mn.
  move:(qle_ltT (Hb _ _ na mN mn) nb) => nc.
  move/(rlt_cQ (proj31_1 nc) (proj32_1 nc)): nc => nd.
  have zr: realp (Vg x m) by apply:BR_seq_prop.
  move:(rlt_ltT (proj2 (the_yp _ _ zr mN)) nd).
  rewrite /BR_seq_of_Q /y !LgV//.
by exists y.
Qed.

Lemma BR_Cauchy_bounded s: CauchyQ s -> exists2 b, ratp b &
   forall n, natp n -> BQabs (Vg s n) <=q b.
Proof.
move => [pa pd].
have H: forall N, natp N -> exists2 b, ratp b &
   forall n, natp n -> n <c N -> BQabs (Vg s n) <=q b.
  apply:Nat_induction; first by exists \0q; [ apply:QS0 | move => n nn /clt0].
  move => n nN [b bq Hrec].
  have /QSa ha: inc (Vg s n) BQ by apply:BQ_seq_prop.
  case:(qleT_ee bq ha) => hb.
    exists (BQabs (Vg s n)) => // m mN /(cltSleP nN) lt. 
    case: (equal_or_not m n) => emn; first by rewrite emn; BQo_tac.
    by apply:(qleT _ hb); apply: (Hrec _ mN).
  exists b => // m mN /(cltSleP nN) lt. 
    by case: (equal_or_not m n) => emn; [rewrite emn | apply: (Hrec _ mN)].
move:(pd _ QpsS1) => [N NN Hb].
move:(H _ NN) => [b1 b1q b1p].
have ha: ratp (Vg s N) by apply:BQ_seq_prop.
set b2:= (BQabs (Vg s N)) +q \1q.
have b2q:= (QSs (QSa ha) QS1).
have [b3 [b3q b1b3 b2b3]]: exists b3, [/\ inc b3 BQ, b1 <=q b3 & b2 <=q b3].
   case:(qleT_ee b1q b2q) => h; [exists b2 | exists b1]; split=> //; BQo_tac.
exists b3 => // n nN.
case: (NleT_el NN nN); last by move => /(b1p _ nN) hc; BQo_tac.
move => Nn.
move: (Hb N n NN nN (cleR (CS_nat NN)) Nn) => hd.
have he: ratp (Vg s n)  by apply:BQ_seq_prop.
move:(qle_triangular ha (QS_diff he ha)).
rewrite (BQsum_diff ha he) (BQabs_diff he ha) => hf.
move/(BQsum_lt2l (proj31_1 hd) (proj32_1 hd) (QSa ha)): hd => [hg _].
exact:(qleT (qleT hf hg) b2b3).
Qed.


Lemma BR_complete1 s: CauchyQ s -> 
  exists2 x, realp x & limitR (BR_seq_of_Q s) x.
Proof.
move => cs.
have [B Bq Bp]:= (BR_Cauchy_bounded cs). 
move:cs => [sa sd].
pose Ap t :=  exists2 n, natp n &
   forall k, natp k -> n <=c k -> (Vg s k) <=q t.
set A := Zo BQ  Ap.
have neA: nonempty A.
  exists B; apply/Zo_P; split => //; exists \0c; [ fprops | move => k kN _].
  by move: (Bp _ kN) => /(BQabs_prop1 (BQ_seq_prop sa kN) Bq) [_].
have Anq: A <> BQ.
  have ha:= (QSo (QSs Bq QS1)).
  case: (inc_or_not (BQopp (B +q \1q)) A); last by move => hb h; case: hb; ue.
  move => /Zo_P [_ [n nN np]].
  have hc: BQopp (B +q \1q) <q BQopp B by apply/ qlt_opp; apply:(qlt_succ Bq).
  move/(BQabs_prop1 (BQ_seq_prop sa nN) Bq):(Bp _ nN) => [hb _].
  move:(qle_ltT (np _ nN (cleR (CS_nat nN))) hc) => hd; BQo_tac.
have As1: forall x y, inc x A -> x <=q y -> inc y A.
  move => x y /Zo_P [xq [n na nb]] xy; apply /Zo_P; split.
    apply:(proj32 xy).
  exists n => // k ka kb; move: (nb _ ka kb) => ha; BQo_tac.
have As: forall x y, inc x A -> x <q y -> inc y A.
  move => x y xa [xy _]; apply: (As1 _ _ xa xy).
case:(p_or_not_p (exists2 y, inc y A & forall t, inc t A -> y <=q t)).
  move =>[y / Zo_P[ya yb] yc] ;move:(RS_of_Q ya) => yr. 
  exists (BR_of_Q y) => // e eq; ex_middle bad.
  have hep:=(BQhalf_pos eq).
  have heq:= (BQps_sBQ hep).
  have [N NN HN]:=(sd _ hep).
  have[n [nN ha hb]]: exists n, [/\ inc n Nat, N <=c n &  (Vg s n) <=q y -q e].
    move: yb => [m ma mb].
    move:(cmax_p1 (CS_nat ma)(CS_nat NN)); set q := cmax _ _.  
    move => [ka kb].
    have qN: natp q by apply:Gmax_E.
    ex_middle bad2; case: bad; exists q => // k kN lnk.
    have ha: ratp (Vg s k) by apply: BQ_seq_prop.
    have hb: inc (y -q Vg s k) BQp.
      apply/(qle_diffP ha ya); apply: mb => //; exact: (cleT ka lnk).
    rewrite /BR_seq_of_Q LgV// (BRdiff_cQ ha ya).
    rewrite (BRabs_cQ (QS_diff ha ya)) (BQabs_diff ha ya) (BQabs_pos hb).
    move: (BQp_sBQ hb) (BQps_sBQ eq) => su sv.
    apply/(rlt_cQ su sv);case: (qleT_el sv su) => // /(qle_diffP1 sv su).
    rewrite - (BQdiff_diff2 ya ha sv) BQsumC (BQdiff_diff2 ya  sv ha).
    move /(qle_diffP1 ha (QS_diff ya sv)) => hd.
    case: bad2;exists k; split => //; exact: (cleT kb lnk).
  have [m [mN hm1 hm2]]: exists m, 
      [/\ natp m, N <=c m &  y -q (BQhalf e) <q (Vg s m)].
    have hc:= (BQsum_Mps ya hep).
    case: (inc_or_not (y -q BQhalf e) A).
      move => /yc h; move/(BQsum_le2r ya (proj32 h) heq): h.
      rewrite (BQsum_diff1 heq ya) => hd; BQo_tac.
    have dq:=(QS_diff ya heq).
    move => bad2; ex_middle bad3; case bad2; apply:(Zo_i dq). 
    exists N => // k ka kb;case:(qleT_el (BQ_seq_prop sa ka) dq) => // he.
    case: bad3; exists k; split => //.
  move:(proj1 (HN _ _ nN mN ha hm1)). 
  move/(BQabs_prop1 (QS_diff  (proj31 hb) (proj32_1 hm2)) heq) => [hc _].
  move:(qlt_opp hm2); rewrite (BQoppB ya heq) => hd.
  move:(BQsum_Mlelt hb hd); rewrite - /(_  -q _).
  rewrite - {1} (BQdouble_half1 (BQps_sBQ eq))(BQdiff_diff2 ya heq heq).
  rewrite - (BQoppB ya heq) -/(_ -q _)(BQdiff_sum (proj31_1 hm2) (QSo heq)).
  move => he; BQo_tac.
move => Ar1.
have /BR_P Ar: real_dedekind A. 
   split => //; [ apply:Zo_S | move => x xa; ex_middle u; case: Ar1].
   exists x => // t ta; case:(qleT_el (Zo_S xa)  (Zo_S ta)) => // tx.
   case:u;ex_tac.
exists A => // e ep.
move:(BQhalf_pos ep)(BQhalf_pos1 ep) => hep lt0.
move:(sd _ hep) => [N NN Hn]; exists N => // n nN lenn.
move/(rlt_cQ (proj31_1 lt0) (proj32_1 lt0)): lt0.
apply: rle_ltT.
have heq:=(BQps_sBQ hep).
have xq:=(BQ_seq_prop sa nN). 
move: (RS_of_Q xq) (RS_of_Q heq) => xr er.
rewrite /BR_seq_of_Q LgV//; apply/(BRabs_prop1 (RS_diff xr Ar) er).
split. 
  apply /(BRdiff_le2P xr Ar (RSo er)); rewrite /BRdiff (BRopp_K er).
  suff: inc (Vg s n +q (BQhalf e)) A. 
    move => ha;rewrite (BRsum_cQ xq heq);apply:(proj1(BR_le_aux2 Ar ha)).
  apply/Zo_P; split; [ exact (QSs xq heq) |  exists N => // k kN nk ].
  have yq := (BQ_seq_prop sa kN).
  move/(BQabs_prop1 (QS_diff yq xq) heq):(proj1 (Hn _ _ kN nN nk lenn)).
  move => [_ hh]; move/(BQsum_le2l (proj31 hh) (proj32 hh) xq): hh.
  by rewrite (BQsum_diff xq  (BQ_seq_prop sa kN)).
apply/(BRdiff_le1P xr Ar er); rewrite (BRdiff_cQ xq heq). 
apply:(BR_le_aux3 Ar (QS_diff xq heq))  => /Zo_P [_ [m mN hm]].
move:(cmax_p1 (CS_nat mN)(CS_nat NN)); set q := cmax _ _.  
move => [ka kb].
have qN: natp q by apply:Gmax_E.
have yq:= (BQ_seq_prop sa qN).
move/(BQdiff_le2P xq heq yq):(hm _ qN ka) => hb.
move/(BQabs_prop2 (QS_diff xq yq) heq):(Hn _ _ nN qN lenn kb). 
move => [_ h]; BQo_tac.
Qed.


Lemma BR_complete s: CauchyR s -> 
  exists2 x, realp x & limitR s x.
Proof.
move => h.
move:(limitR_same2 h) => [y ya yb].
move:(BR_complete1 ya) => [x xr xv]; exists x => //.
move:(ya) => [yc _].
have ha: BR_seq s by  move: h => [].
have hb: BR_seq (BR_seq_of_Q y) by apply: BR_seq_of_Q_seq.
exact: (limitR_same hb ha xr (similar_seq_sym ha hb yb) xv).
Qed.


(* Continuity *)

Definition BR_near x e y:= realp y /\  BRabs (x -r y) <=r e. 

Lemma BR_nearP x e y: realp x -> realp e ->
  ((BR_near x e y) <-> ( x -r e <=r y /\ y <=r x +r e)).
Proof.
move => xr er; case: (inc_or_not y BR)=> yr; last first.
  split; [ by move => [] | by move => [/proj32 H]].
have ha:=(BRdiff_le1P xr er yr).
have hb: BRopp e <=r x -r y <-> y <=r  x +r e.
  by move:(BRdiff_le2P xr yr (RSo er)); rewrite /BRdiff (BRopp_K er).
split; move=> [sa sb].
    move/(BRabs_prop1 (RS_diff xr yr) er): sb => [su sv]. 
  split; [ by apply/ha | by apply/hb].
split => //; apply/(BRabs_prop1 (RS_diff xr yr) er).
split; [ by apply/hb | by apply/ha].
Qed.

Lemma BR_near_trans x e e' y: e <=r e' ->
  (BR_near x e y) -> (BR_near x e' y).
Proof. move => sa [sb sc]; split => //; BRo_tac. Qed.


Definition continuous_at f x:=
   forall e, inc e BRps -> exists2 d, inc d BRps & 
   forall y,  BR_near x d y ->  BR_near (f x) e (f y).

Definition continuous f:= forall x, realp x -> continuous_at f x.
Definition continuous2 (f:fterm2):= 
  forall x y, realp x -> realp y  -> 
    continuous_at (f x) y /\ continuous_at (f ^~y) x.

Lemma continuous_local f g x: realp x ->
   (exists2 e, inc e BRps & forall y, BR_near x e y -> f y = g y) ->
   continuous_at f x ->  continuous_at g x.
Proof.
move => xr [e ep ev] cfx.
move => e1 e1p.
move:(cfx e1 e1p) => [d dp dv].
move:(rmin_prop2 ep dp) (rmin_prop1 (BRps_sBR ep) (BRps_sBR dp)).
set e2:= (rmin e d); move => sa [sb sc sd]; ex_tac => y ya.
move:(dv _ (BR_near_trans sd ya)).
rewrite (ev _ (BR_near_trans sc ya)).
have hh: BR_near x e2 x. 
   split => //;rewrite (BRdiff_xx xr) BRabs_0; apply/ rle0xP => //. 
   exact:(BRps_sBRp sa).
by rewrite (ev _ (BR_near_trans sc hh)).
Qed.

Lemma continuous_comp f g x:
  continuous_at f x ->  continuous_at g (f x) ->
  continuous_at (g \o f) x.
Proof.
move => ca cb e ep; move:(cb _ ep) => [d dp dv].
move:(ca _ dp) => [e2 e2p e2v]; ex_tac => y ya /=.
by apply: dv; apply: e2v.
Qed.

Lemma continuous2_sym (f:fterm2) : 
  (forall x y, realp x -> realp y  -> f x y = f y x) -> 
  (forall x y, realp x -> realp y  -> 
    continuous_at (f x) y) ->  continuous2 f.
Proof.
move => Ha Hb.
move => x y xr yr; split; first by  apply: Hb.
move => e ep; move:(Hb _ _ yr xr) => h; move:(h _ ep) => [d da db]; ex_tac.
move => t ta; move:(db _ ta). move: (ta) => [tr _].
by rewrite /BR_near (Ha _ _ yr tr)(Ha _ _ yr xr).
Qed.

Lemma continuous2_sum : continuous2 BRsum.
Proof.
apply:continuous2_sym; first by move => x y _ _ ;apply: BRsumC.
move => x y xr yr e ep; ex_tac => z [za zb].
split; [ by apply: RSs | by rewrite BRdiff_sum_simpl_l].
Qed.


Lemma continuous_id: continuous id.
Proof. move => t tr e ep;ex_tac. Qed.


Lemma continuous_opp : continuous BRopp.
Proof.
move => x xr e ep; ex_tac => y [yr].
rewrite (BRabs_diff xr yr)- {1} (BRopp_K yr) /BRdiff BRsumC => h; split => //.
by apply: RSo.
Qed.

Lemma continuous2_diff : continuous2 BRdiff.
Proof.
move => x y xr yr;move:(continuous2_sum xr (RSo yr)) => [sa sb].
split => //; apply:(continuous_comp  (continuous_opp yr) sa).
Qed.


Lemma continuous2_prod : continuous2 BRprod.
Proof.
apply:continuous2_sym; first by move => x y _ _ ;apply: BRprodC.
move => x y xr yr e ep. 
set e1 := Yo (x = \0r) \1r (e /r (BRabs x)).
have ha : x <> \0r -> BRabs x <> \0r by move/(BRabs0_bis xr). 
have e1p: inc e1 BRps.
   rewrite /e1; Ytac h; [  apply: RpsS1 |apply:(RpsS_div ep); apply/BRps_iP ].
   split; [apply: (RpSa xr) | by apply: ha].
ex_tac; move=> z [zr zb]; split; first by apply:RSp.
rewrite - (BRprodBr xr yr zr) (BRprod_abs xr (RS_diff yr zr)).
case: (equal_or_not x \0r) => sa.
   rewrite sa BRabs_0 BRprod_0l; apply/ rle0xP => //; exact:(BRps_sBRp ep).
move: (BRprod_Mlege0 (RpSa xr) zb); rewrite BRprodC /e1; Ytac0.
by rewrite (BRprodC _ (BRabs x)) (BRprod_div (RSa xr) (BRps_sBR ep) (ha sa)). 
Qed.

Lemma continuous_inv x: realp x -> x <> \0r -> continuous_at BRinv x.
Proof.
move => xr xnz e ep. 
have ha: inc (BRabs x) BRps by apply:  RpsSa.
set e1 := BRhalf (BRabs x).
have e1ps: inc e1 BRps by apply: BRhalf_pos.
set e2 := e *r (BRabs x) *r e1.
have e2ps: inc e2 BRps by exact: (RpsS_prod (RpsS_prod ep ha) e1ps).
move:(rmin_prop2 e1ps e2ps) (rmin_prop1 (BRps_sBR e1ps) (BRps_sBR e2ps)).
set e3:= (rmin e1 e2); move => sa [sb sc sd]; ex_tac => y [yr ya].
move: (RSa xr)(RSa yr) (proj32 sc)  => axr ayr e1r.
have hb: BRhalf (BRabs x) <=r BRabs y.
  move:(rle_triangular (RS_diff xr yr) yr); rewrite (BRsum_diff1 yr xr).
  move/(BRsum_le2r (proj31 ya) (proj32 sc) ayr):(rleT ya sc) => l1 l2.
  move:(rleT l2 l1); rewrite - {1} (BRdouble_half1 axr)  -/e1 => l3.
  by apply/(BRsum_le2l e1r ayr e1r).
have ynz: y <> \0r.
  move/ rlt0xP:e1ps => h1 h;move: hb; rewrite h BRabs_0 -/e1 => h2; BRo_tac.
have pnz: x *r y <> \0r by apply: BRprod_nz.
move: (RSp xr yr)  (proj32 sd) => xyr e2r.
have hc1: inc  (BRabs (x *r y)) BRps by apply: RpsSa.
have hc: inc (BRinv (BRabs (x *r y))) BRps by  apply:RpsS_inv.
move/BRps_iP: hc1 => [/BRp_sBR hca hcb].
move/(BRprod_ple2r (proj31 ya) e2r hc):(rleT ya sd).
have hd: inc (e *r BRabs x) BRps by apply: RpsS_prod.
move/ (BRprod_Mgt0le e1r ayr hd): hb.
rewrite -/e2  -(BRprodA (BRps_sBR ep) axr ayr). 
rewrite - (BRprod_abs xr yr) => he.
move: (BRprod_ple2r (proj31 he) (proj32 he) hc); rewrite (BRprodC e).
rewrite -/(_ /r _) -/(_ /r _) (BRdiv_prod hca (BRps_sBR ep) hcb).
rewrite (BRprodC _ e) => hf; move/hf: he => hg.
move => eq;split; first by apply:RS_inv.
rewrite (BRinv_diff xr yr xnz ynz) - (BRdiv_abs (RS_diff yr xr) xyr).
rewrite (BRabs_diff yr xr); BRo_tac.
Qed.

Lemma continuous2_div x y: realp x -> realp y ->
    (continuous_at (BRdiv ^~y) x) /\(y <> \0r -> continuous_at (BRdiv x) y).
Proof.
move => xr yr; rewrite /BRdiv.
move:(continuous2_prod xr (RS_inv yr)) => [sa sb].
split => // ynz; exact:(continuous_comp  (continuous_inv yr ynz) sa).
Qed.


Lemma continuous_real f x: realp x ->  continuous_at f x -> realp (f x).
Proof.
move => xr h1; move:(h1 _ RpsS1) => [d /BRps_sBRp de h2].
have /h2 [//]: (BR_near x d x). 
by split => //; rewrite BRdiff_xx // BRabs_0; apply/ rle0xP. 
Qed.


Lemma continuous_sum f g x: realp x ->
   continuous_at f x -> continuous_at g x ->
   continuous_at (fun z => f z +r g z) x.
Proof.
move => xr  pa pb.
move => e ep; move: (BRhalf_pos ep) => hep.
move:(pa _ hep)(pb _ hep) =>[d1 d1ps d1v] [d2 d2ps d2v].
move:(rmin_prop2 d1ps d2ps) (rmin_prop1 (BRps_sBR d1ps) (BRps_sBR d2ps)).
set d3:= (rmin d1 d2); move => sa [sb sc sd]; ex_tac => y [yr ya].
have ha: BR_near x d1 y by split => //; BRo_tac.
have hb: BR_near x d2 y by split => //; BRo_tac.
move:(d1v _ ha) (d2v _ hb) => [ua ub] [uc ud].
move:(continuous_real xr pa)(continuous_real xr pb) => fxr gxr.
split; first by apply: RSs.
rewrite /BRdiff (BRoppD ua uc).
rewrite (BRsum_ACA fxr gxr (RSo ua)  (RSo uc)). 
move:(rle_triangular (RS_diff fxr ua) (RS_diff gxr uc)).
move:(BRsum_Mlele ub ud); rewrite (BRdouble_half1 (BRps_sBR ep)).
move => h1 h2; BRo_tac. 
Qed.


Lemma continuous_diff f g x:  realp x ->
   continuous_at f x -> continuous_at g x ->
   continuous_at (fun z => f z -r g z) x.
Proof.
move => xr  pa pb.
apply:(continuous_sum xr pa); apply: (continuous_comp pb).
apply: continuous_opp; apply:(continuous_real xr pb).
Qed.


Lemma continuous_prod f g x:  realp x ->
   continuous_at f x -> continuous_at g x ->
   continuous_at (fun z => f z *r g z) x.
Proof.
move => xr  pa pb.
move:(continuous_real xr pa) (continuous_real xr pb) => fxr gxr.
move: (RSa gxr) => agxr.
set v0 :=  BRabs (g x) +r \1r.
have v0p: inc v0 BRps by apply:(RpsS_sum_r (RpSa gxr) RpsS1).
set v1 := BRabs (g x) +r v0.
have v1p: inc v1 BRps by exact :(RpsS_sum_r (RpSa gxr) v0p). 
set v2 := BRabs (f x) +r \1r.
have v2a: BRabs (f x) <r v2 by  exact:(BRsum_Mps (RSa fxr) RpsS1).
have v2p: inc v2 BRps by apply:(RpsS_sum_r (RpSa fxr) RpsS1).
move => e ep; move: (BRhalf_pos ep) => hep.
set e1 := (BRhalf e) /r v1.
set e2 := ((BRhalf e) /r v2). 
have e1ps: inc e1 BRps by apply:RpsS_div.
have e2ps: inc e2 BRps by apply:RpsS_div.
move:(rmin_prop2 e2ps v0p) (rmin_prop1 (BRps_sBR e2ps) (BRps_sBR v0p)).
set e3:= (rmin e2 v0); move => e3ps [e3r e3a e3b].
move:(BRps_sBR hep) => her.
have e3p1: e3 *r BRabs (f x) <r BRhalf e.
  move:(BRprod_Mltgt0 (RpsS_div hep v2p) v2a); rewrite BRprodC.
  rewrite (BRprod_div  (BRps_sBR v2p) her (BRps_nz v2p)).
  move:(BRprod_Mlege0 (RpSa fxr) e3a) => sa sb; BRo_tac.
move: (pa _ e1ps) => [d1 d1ps d1v].
move: (pb _ e3ps) => [d2 d2ps d2v].
move:(rmin_prop2 d1ps d2ps) (rmin_prop1 (BRps_sBR d1ps) (BRps_sBR d2ps)).
set d3:= (rmin d1 d2); move => sa [sb sc sd]; ex_tac => y [yr ya].
have ha: BR_near x d1 y by split => //; BRo_tac.
have hb: BR_near x d2 y by split => //; BRo_tac.
move:(d1v _ ha)(d2v _ hb) => [fyr le1] [gyr le2].
have Ha: BRabs (f x *r (g x -r g y)) <r BRhalf e.
   rewrite (BRprod_abs fxr (RS_diff gxr gyr)).
   rewrite BRprodC; exact: (rle_ltT (BRprod_Mlege0 (RpSa fxr) le2) e3p1).
move: (RS_diff gyr gxr) (RS_diff fxr fyr) => u1r u2r.
have Hb: BRabs (g y) <=r v1.
  move:(rle_triangular u1r gxr).
  rewrite (BRsum_diff1 gxr gyr) (BRabs_diff gyr gxr).
  move/(BRsum_le2r (proj31 le2) (proj32 e3b) agxr): (rleT le2 e3b).
  rewrite (BRsumC v0) => hhb hhc; BRo_tac.
have Hc: BRabs ((f x -r f y) *r g y) <=r BRhalf e.
  rewrite (BRprod_abs u2r gyr).
  move:(BRprod_Mlelege0 (BRps_sBRp e1ps) (RpSa gyr) le1 Hb).
  by rewrite (BRprodC _ v1) (BRprod_div(BRps_sBR v1p) her (BRps_nz v1p)).
split; first by apply:RSp.
move:(BRsum_Mlele (proj1 Ha) Hc); rewrite (BRdouble_half1 (BRps_sBR ep)).
apply:rleT; move:(rle_triangular (RSp fxr (RS_diff gxr gyr)) (RSp u2r gyr)).
move: (RSp fxr gxr) (RSp fxr gyr) (RSp fxr gyr) (RSp fyr gyr) => ar br cr dr.
rewrite (BRprodBl gyr fxr fyr) (BRprodBr fxr gxr gyr).
by rewrite (BRsumA (RS_diff ar br) br (RSo dr)) (BRsum_diff1 br ar).
Qed.


Lemma continuous_div f g x:  realp x -> g x <> \0r ->
   continuous_at f x -> continuous_at g x ->
   continuous_at (fun z => f z /r g z) x.
Proof.
move => xr gnz pa pb.
apply:(continuous_prod xr pa); apply: (continuous_comp pb).
apply: (continuous_inv (continuous_real xr pb) gnz).
Qed.

Lemma continuous_square: continuous BRsquare.
Proof. by move => x xr; have h:=(continuous_id xr);apply:continuous_prod. Qed.


Lemma continuous_prop1 f x a: continuous_at f x -> a <r f x ->
  exists2 e, inc e BRps & forall y, (BR_near x e y) -> a <r f y.
Proof.
move => ha hb.
move:(hb) =>[[ar fxr _] _ ].
have ep: inc (f x -r a) BRps by apply/ rlt0xP; apply/(rlt_diffP1 ar fxr).
have hep:=(BRhalf_pos ep).
have her:=(BRps_sBR hep).
move:(ha _ hep) => [d dp dv]; ex_tac => y /dv [ya yb].
move/ rlt0xP: hep => hep.
move/ (BRabs_prop3 fxr ya her): yb => [ _ la].
move:(BRsum_Mlegt0 la hep). 
rewrite - (BRsumA ya her her) (BRdouble_half1 (BRps_sBR ep)) /BRdiff.
rewrite (BRsumC (f x)) (BRsumA ya (RSo ar) fxr) => hc.
move/(rlt_diffP1 fxr (proj32_1 hc)) : hc.
by rewrite( BRdiff_sum1 fxr (RS_diff ya ar)) => /(rlt_diffP1 ar ya).
Qed.


Lemma continuous_prop2 f x a: continuous_at f x -> f x <r a ->
  exists2 e, inc e BRps & forall y, (BR_near x e y) -> f y <r a.
Proof.
move => ha lt1. 
have fr: realp (f x) by BRo_tac.
pose g x := BRopp (f x).
have ra:= (continuous_comp ha (continuous_opp fr)).
move:(continuous_prop1 ra (rlt_opp lt1)) => [e ep h].
move:(ha _ ep) => [d dp dq].
move:(rmin_prop2 dp ep) => mp.
move:(rmin_prop1 (BRps_sBR dp) (BRps_sBR ep)) => [_ sa sb].
ex_tac => y yn; move:(dq _ (BR_near_trans sa yn)) =>[fyr _].
by move:(h _ (BR_near_trans sb yn)) =>/(rlt_oppP fyr (proj32_1 lt1)).
Qed.



Definition continuous_right f x:=
   forall e, inc e BRps -> exists2 d, inc d BRps & 
   forall y,  BR_near x d y ->  x <=r y -> BR_near (f x) e (f y).

Definition continuous_left f x:=
   forall e, inc e BRps -> exists2 d, inc d BRps & 
   forall y,  BR_near x d y -> y <=r x -> BR_near (f x) e (f y).

Definition Bolzano_hyp f x y:=
    [/\ continuous_right f x, continuous_left f y &
    (forall z, x <r z -> z <r y -> continuous_at f z)].

Lemma Bolzano_hyp_simp f x y: x <=r y ->
    (forall z, x <=r z -> z <=r y -> continuous_at f z) ->
    Bolzano_hyp f x y.
Proof.
move => xy h; move:(xy) => [rx ry _];split.
+ move => e ep; move: (h _ (rleR rx) xy) => cf; move: (cf e ep).
  move => [d da db]; ex_tac.
+ move => e ep; move: (h _ xy (rleR ry)) => cf; move: (cf e ep).
  move => [d da db]; ex_tac.
+ by move => z [za _] [zb _]; apply: h.
Qed.

Lemma Bolzano f x y:  x <=r y -> Bolzano_hyp f x y ->
    f x <=r \0r -> \0r <=r f y ->
    exists2 z, (x <=r z /\ z <=r y) & f z = \0r.
Proof.
move => xy [Ha Hb Hc] la lb.
set E1:= Zo BR (fun z => (x <=r z /\ z <=r y)).
set E2:= Zo E1 (fun z => \0r <=r f z).
have xr: realp x by BRo_tac.
have yr: realp y by BRo_tac.
have ha: sub E2 BR by move => t /Zo_S /Zo_S.
move: BR_osr => [or sor].
have ye2: inc y E2 by apply:Zo_i => //; apply:Zo_i => //;split => //; BRo_tac.
have hb: nonempty E2 by exists y.
have hc1: lower_bound BR_order E2 x.
  split; first by rewrite sor.
  by move => t /Zo_S /Zo_P[ _ [ub uc]]; apply /BR_gleP.
have hc: bounded_below BR_order E2  by exists x.
have hd: sub E2 (substrate BR_order) by move => t /Zo_S /Zo_S; rewrite sor.
move: (BR_inf_exists ha hb hc) => [z /(glbP or hd)].
rewrite /lower_bound sor; move => [[zr za] zb].
move: (za _ ye2) => /BR_gleP lzy.
move:hc1; rewrite/lower_bound sor => /zb /BR_gleP lxz.
have fzr: realp (f z).
   case: (equal_or_not x z) => ea; first by rewrite - ea; BRo_tac.
   case: (equal_or_not z y) => eb; first by rewrite  eb; BRo_tac.
   apply:(continuous_real zr (Hc _  (conj lxz ea) (conj lzy eb))).
case: (rleT_ell fzr RS0) => cp1.
+ by exists z.
+ case: (equal_or_not z y) => eb. 
    move: lb; rewrite - eb => he; BRo_tac.
  have zyp: inc (y -r z) BRps by  apply/ rlt0xP; apply/ rlt_diffP1.
  have  [e ep ev]: exists2 e, inc e BRps & 
      forall t, (BR_near z e t) -> z <r t  -> f t <r \0r.
    case: (equal_or_not x z) => ea; last first.
      move: (continuous_prop2 (Hc _  (conj lxz ea) (conj lzy eb)) cp1).
      by move => [e ep eh]; exists e => // t ta _; apply: eh.
    move / rgt0xP: cp1; rewrite - ea => hb1.
    move:(BRhalf_neg hb1) => / rgt0xP hn.
    have ep: inc (BRopp (f x)) BRps by apply:BRopp_negative1.
    have hep:=(BRhalf_pos ep).
    have her:= (BRps_sBR hep).
    have fxr := (BRms_sBR hb1); have hfxr:=(RS_half fxr).
    move:(Ha _ hep) => [d dp dv]; ex_tac => t ta tb. 
    move:(dv _ ta (proj1 tb)) => [ya yb].
    move/  rlt0xP: hep => hep.
    move:(rle_abs (RS_diff ya fxr));rewrite (BRabs_diff ya fxr) => yc.
    move/(BRsum_le2r (proj31 yc) her fxr):  (rleT yc yb).
    rewrite (BRsum_diff1 fxr ya); rewrite - {2} (BRdouble_half1 fxr).
    rewrite (BRhalf_opp fxr) BRsumC -/( _ -r _) BRdiff_sum // => he; BRo_tac.
  move:(rmin_prop2 ep zyp) (rmin_prop1 (BRps_sBR ep) (BRps_sBR zyp)).
  set t := (rmin e (y -r z)); move => tp [tr tb tc].
  have te: z <r (z +r t) by exact: (BRsum_Mps zr tp).
  have td: (z +r t) <=r y. 
    by move/(BRsum_le2l tr (RS_diff yr zr) zr): tc; rewrite (BRsum_diff zr yr).
  have tf: realp (z +r t) by apply:RSs.
  have tg: BR_near z e (z +r t). 
    split => //.
    rewrite /BRdiff (BRoppD zr tr) (BRsumC (BRopp z)).
    by rewrite (BRsum_diff zr (RSo tr))(BRabs_opp tr)(BRabs_pos (BRps_sBRp tp)).
  have sa:= (ev _ tg te).
  have er:=(BRps_sBR ep).
  suff th:(forall u, inc u E2 -> gle BR_order (z +r t) u).
    move: (zb (z +r t) (conj tf th)) => /BR_gleP ti; BRo_tac.
  move => u /Zo_P [/Zo_P [ua [ub uc]] ud]; apply/BR_gleP.
  case: (rleT_el tf ua) => // ue.
  case: (rleT_ell zr ua) => uf.
  - move: cp1; rewrite uf => cp1; BRo_tac.
  - have zu: BR_near z e u.
      split => //; apply/(BRabs_prop3 zr ua er); split.
        move/(BRsum_le2r  tr er zr): tb; rewrite BRsumC  => th.
        move:(rleT (proj1 ue) th) => ti.
        move/(BRsum_le2r ua (proj32 ti) (RSo er)): ti.
        by rewrite -/( _ -r _)  -/( _ -r _) BRdiff_sum.
      exact (proj1 (rlt_ltT uf (BRsum_Mps ua ep))).
    move:(ev _ zu uf) => ug; BRo_tac.
  - have te2: inc u E2 by apply:Zo_i => //; apply:Zo_i.
    move:(za _ te2) => /BR_gleP ug; BRo_tac.
+ case: (equal_or_not x z) => ea. 
   by move: la; rewrite ea => he; BRo_tac.
  have zxp: inc (z -r x) BRps by apply/ rlt0xP; apply/ rlt_diffP1.
  have [e ep ev]: exists2 e, inc e BRps & 
      forall t, (BR_near z e t) -> t <r z -> \0r <r f t.
    case: (equal_or_not z y) => eb.
       rewrite eb.
       have ep: inc (f z) BRps by apply/ rlt0xP.
       have hep:=(BRhalf_pos ep).
       have her:= (BRps_sBR hep).
       move:(Hb _ hep) => [d dp dv];ex_tac => t ta tb. 
       move:(dv _ ta (proj1 tb)) => [ya yb].
       move/  rlt0xP: hep => hep.
       move/ (BRabs_prop3 (proj32 lb) ya her): yb => [ _].
       rewrite - eb - {1} (BRdouble_half1  (BRps_sBR ep)).
       move/(BRsum_le2r her ya her) => hc1; BRo_tac.
    move: (continuous_prop1 (Hc _  (conj lxz ea) (conj lzy eb)) cp1).
    by move => [e ep eh]; exists e => // t ta _; apply: eh.
  move:(rmin_prop2 ep zxp) (rmin_prop1 (BRps_sBR ep) (BRps_sBR zxp)).
  set t := (rmin e (z -r x)); move => tp [tr tb tc].
  have td:  x <=r (z -r t) by apply /(BRdiff_le2P zr tr xr).
  have te:= (BRsum_Mms zr (BRopp_positive1 tp)).
  have tf:= (proj31_1 te).
  have tg: BR_near z e (z -r t).
    split => //.
    by rewrite (BRdiff_diff zr zr tr) (BRdiff_xx zr) (BRsum_0l tr) (BRabs_poss).
  move:(ev _ tg te) => [th _].
  have /za /BR_gleP /(rleNgt) //: inc  (z -r t) E2. 
  by apply:Zo_i => //; apply:Zo_i => //; split => //;apply:(rleT (proj1 te)).
Qed.


Lemma Bolzano1 f x y:  x <=r y ->
    (forall z, x <=r z -> z <=r y -> continuous_at f z) ->
    f x <=r \0r -> \0r <=r f y ->
    exists2 z, (x <=r z /\ z <=r y) & f z = \0r.
Proof.
move => xy /(Bolzano_hyp_simp xy) Hc la lb; apply: Bolzano => //.
Qed.

Definition BR_between x a b:= (a <=r x /\ x <=r b) \/ (b <=r x /\ x <=r a). 

Lemma Bolzano2 f x y v:  x <=r y -> Bolzano_hyp f x y ->
    (BR_between v (f x) (f y)) ->
    exists2 z, (x <=r z /\ z <=r y) & f z = v.
Proof.
move => lexy; move: f v.
suff:forall f v, Bolzano_hyp f x y -> ((f x) <=r v /\ v <=r (f y)) ->
   exists2 z, x <=r z /\ z <=r y & f z = v.
  move => H f v Ha; case;first by  apply:H.
  move => [ha hb].
  pose g z := BRopp (f z).
  have hc: g x <=r (BRopp v) /\ (BRopp v) <=r g y by split; apply :rle_opp.
  move: Ha => [H1 H2 H3].
  move: (ha) => [fyr vr _].
  have H1': continuous_right g x.
    move => e ep; move: (H1 e ep) => [d dp dv]; ex_tac => z za zb.
    move:(dv _ za zb) => [hu uv]; rewrite /g; split; first by apply:RSo.
    rewrite /BRdiff (BRopp_K hu) BRsumC.
    by move: uv;  rewrite (BRabs_diff (proj32 hb) hu). 
  have H2': continuous_left g y.
     move => e ep; move: (H2 e ep) => [d dp dv]; ex_tac => z za zb.
     move:(dv _ za zb) => [hu uv]; rewrite /g; split; first by apply:RSo.
     rewrite /BRdiff (BRopp_K hu) BRsumC.
     by move: uv;  rewrite (BRabs_diff fyr hu). 
  have H3': forall z, x <r z -> z <r y -> continuous_at g z.
    move => z za zb; move: (H3 _ za zb) => h1. 
   apply:(continuous_comp(H3 _ za zb));apply:continuous_opp.
    apply:(continuous_real (proj32_1 za) h1).
  have hd: Bolzano_hyp g x y by split.
  move:(H _ _ hd hc) => [z za zb];exists z => //;apply BRopp_inj => //.
  case:(equal_or_not x z) => lxz; first by rewrite - lxz; exact (proj32 hb).
  case:(equal_or_not z y) => lzy; first by rewrite  lzy.
  move: (H3 _ (conj (proj1 za) lxz)  (conj (proj2 za) lzy)).
  by move/ (continuous_real (proj32 (proj1 za)) ). 
move => f v [Ha Hb Hc] [fxv fyv].
move: (fxv) => [fxr vr _].
move:(RSo vr) => ovr.
pose g z := f z +r (BRopp v).
have Ha': continuous_right g x.
  move => e ep; move:(Ha e ep) => [d dp dv]; exists d => // z za zb.
  move:(dv _ za zb) => [zc zd]; split; first by apply:RSs.
  by rewrite /g BRdiff_sum_simpl_r.
have Hb': continuous_left g y.
  move => e ep; move:(Hb e ep) => [d dp dv]; exists d => // z za zb.
  move:(dv _ za zb) => [zc zd]; split; first by apply:RSs.
  rewrite /g BRdiff_sum_simpl_r => //; BRo_tac.
have H': Bolzano_hyp g x y.
  split => // z za zb; move:(Hc _ za zb) => cc. rewrite /g.
  move:(proj2 (continuous2_sum  (continuous_real (proj32_1 za) cc) ovr)) => h.
  exact:(continuous_comp cc h).  
have ha: g x <=r \0r.
  move/(BRsum_le2r (proj31 fxv) (proj32 fxv) ovr): fxv.
    by rewrite BRsum_opp_r.
have hb:  \0r <=r g y by move/(rle_diffP1 vr (proj32 fyv)): fyv.
move: (Bolzano lexy H' ha hb) => [z [za zb] zc]; exists z => //.
apply:BRdiff_xx_rw => //.
case: (equal_or_not x z) => exz; first by ue.
case: (equal_or_not z y) => ezy; first by rewrite ezy; BRo_tac.
exact:(continuous_real (proj32 za) (Hc _ (conj za exz) (conj zb ezy))).
Qed.

Lemma BRsqrt_exists x: inc x BRp -> exists2 y, inc y BRp & x = BRsquare y.
Proof.
move => xr.
have ha:  \0r <=r x by apply / rle0xP.
have hb:  BRsquare \0r <=r x by rewrite /BRsquare BRprod_0r. 
have [y xy fy]: exists2 y, \0r <=r y & x <=r BRsquare y.
  case: (rleT_ee (BRp_sBR xr) RS1) => h.
    exists \1r; first by  apply/ rle0xP; exact:(BRps_sBRp RpsS1). 
    by rewrite /BRsquare (BRprod_1r RS1).
  by exists x => //; move:(BRprod_Mlege0 xr h);rewrite (BRprod_1l (proj32 h)). 
have hc: (forall z, \0r <=r z -> z <=r y -> continuous_at BRsquare z).
  by move => z [_ za _] _; move:(continuous_square za). 
have hd:(BR_between x (BRsquare \0r) (BRsquare y)) by left.
move:(Bolzano2 xy (Bolzano_hyp_simp xy hc) hd) => [z [/ rle0xP za _] zb].
ex_tac. 
Qed.

(* ne sert a rien *)
Lemma inf_of_continuous f a x
   (y := infimum BR_order (Zo BR (fun t => a <=r t /\ x <=r f t ))) : 
   (forall t, realp t -> realp (f t)) ->
   (forall t, a <=r t -> continuous_at f t) ->
   (exists2 b, a <r b  & x <=r f b) ->
   (a <r x) -> (f a <r x) ->
   a <r y /\ x = f y.
Proof.   
move => fr fc fb xs fxs.
rewrite /y; set A := Zo _ _; clear y. 
have xr:=(proj32_1 xs).
have [or sr] := BR_osr.
have ha: sub A BR by move => t /Zo_S. 
have hd: sub A (substrate BR_order) by ue.
have hb: nonempty A. 
  move: fb=> [b ba bb]; exists b; apply:Zo_i; first by exact:(proj32_1 ba).
  split => //; BRo_tac.
have ar: realp a by exact:(proj31_1 xs). 
have hc1: inc a BR /\ (forall y, inc y A -> gle BR_order a y).
  split; [ exact | by move => t/Zo_P [_ [ /BR_gleP ]]].
have hc: bounded_below BR_order A by exists a; hnf; rewrite sr.
move: (infimum_pr1 or (BR_inf_exists  ha hb hc)). 
set y := (infimum BR_order A); move/(glbP or hd);rewrite /lower_bound. 
rewrite sr; move => [[yr sb] sc].
move: (sc _ hc1) => /BR_gleP lay.
have lay': a <r y.
  split => // eay.  
  move:(continuous_prop2 (fc _ (rleR ar)) fxs) => [e ea eb].
  move/ rlt0xP:ea => ep; move:(BRsum_Mlegt0 lay ep) => le1.
  have er := (proj32_1 ep).
  have aer:=(RSs ar er).
  suff: a +r e <=r y by move: le1;rewrite eay => le1 le2;BRo_tac.
  apply/BR_gleP; apply:sc; split => // z /Zo_P [za [zb zc]]; apply/BR_gleP.
  case:(rleT_ee aer za) => // le2.
  suff: (BR_near a e z) by move/eb => le3; BRo_tac.
  apply/(BR_nearP _ ar er); split=> //.
  apply/(BRsum_le2r (RS_diff ar er) za er).
  rewrite BRsumC BRsum_diff //; exact:(proj1(BRsum_Mlegt0 zb ep)). 
split => //.
have ysr := (fr _ yr).
case: (rleT_ell xr ysr) => // le.
  move /(rlt_diffP xr ysr): (le) => ep. 
  have ep1:=(BRhalf_pos  ep).
  have [d dp de]:=(fc _ lay _ ep).
  have he: forall z, BR_near y d z -> x <=r f z.
    move => z /de [za zb]. apply/(rle_oppP xr za)/(rle_diffP1 (RSo za)(RSo xr)).
    rewrite -(BRdiff_sum_simpl_r (RSo xr)(RSo za) ysr) BRsumC (BRsumC _ (f y)).
    apply/(rle_diffP1 (RS_diff ysr za) (RS_diff ysr xr)).
    apply:(rleT (rle_abs (RS_diff ysr za)) zb).
  suff:(exists z, inc z A /\ z <r y) by move=> [z [/sb/BR_gleP za] zb]; BRo_tac.
  have dr:=(BRps_sBR dp).
  have le3:a <=r y +r d by exact:(proj1(rlt_ltT lay' (BRsum_Mps yr dp))).
  have le4: y -r d <r y by apply:(BRsum_Mms yr); apply:BRopp_positive1.
  case:(rleT_ee (RS_diff yr (BRps_sBR dp)) ar) => le2. 
     exists a; split => //; apply/Zo_P; split => //; split; first by BRo_tac.
     by apply:he;apply/BR_nearP.
  move:(proj32 le2) => ydr.  
  have lt4: x <=r f (y -r d). 
    apply: he; split => //.
    by rewrite BRdiff_diff_simp // (BRabs_pos (BRps_sBRp dp)); apply: rleR.
  by exists (y -r d); split => //; apply/Zo_P.
move: (continuous_prop2 (fc _ lay) le) => [e eps eb].
have er:= BRps_sBR eps.
suff: gle BR_order (y +r e) y. 
  move/BR_gleP;move:(BRsum_Mps yr eps) => la lb; BRo_tac.
have yer: realp (y +r e) by apply:RSs.
apply:sc; split => // z zA;apply/BR_gleP.
move:(sb _ zA) => /BR_gleP lt1; move/Zo_P: zA => [zr [laz zc]].
case: (rleT_ee yer zr)=> // le2.
have le3:=  (BRms_sBRm (BRopp_positive1 eps)).
have le4: y -r e <=r z by apply:(rleT (BRsum_Mm yr le3) lt1).
have:(BR_near y e z) by apply/(BR_nearP _ yr er). 
move/eb => w; BRo_tac.
Qed.

(* bof *)

Lemma BRsqrt_exists2 x
   (y := infimum BR_order (Zo BRp (fun z => x <=r BRsquare z))) : 
   inc x BRp -> inc y BRp /\ x = BRsquare y.
Proof.
move:BR_osr => [or sr].
rewrite /y; set A := Zo _ _; clear y => xp; move: (BRp_sBR xp) => xr.
have ha: sub A BR by move => t /Zo_S /BRp_sBR. 
have hd: sub A (substrate BR_order) by ue.
have hb: nonempty A.
  have bp2 :=(BRps_sBRp RpsS1). 
  have bp1:=(RpS_sum (RpS_square RS1)(RpS_square xr)).
  exists (\1r +r x); apply:Zo_i; first by apply:RpS_sum.
  rewrite (BRsum_square RS1 xr) (BRprod_1l xr) BRdouble_C -(BRdouble_s xr).
  rewrite (BRsumA (BRp_sBR bp1) xr xr) BRsumC. 
  apply:(BRsum_Mp xr (RpS_sum bp1 xp)).
have hc1: inc \0r BR /\ (forall y, inc y A -> gle BR_order \0r y).
  by split;[ exact:RS0 | move => t /Zo_S / rle0xP/BR_gleP].
have hc: bounded_below BR_order A by exists \0r;hnf;rewrite sr.
move: (infimum_pr1 or (BR_inf_exists  ha hb hc)). 
set y := (infimum BR_order A); move/(glbP or hd);rewrite /lower_bound. 
rewrite sr; move => [[sa sb] sc].
move: (sc _ hc1) => /BR_gleP / rle0xP y0; split; first exact.
have yr := (BRp_sBR y0); have ysp:= (RpS_square yr); have ysr:=(BRp_sBR ysp).
case: (equal_or_not x \0r) => xnz.
  have ww: BRsquare \0r = \0r by rewrite /BRsquare BRprod_0l.
  case: (equal_or_not y \0r) => ynz; first by rewrite xnz ynz ww.
  have yps: inc y BRps by apply /BRps_iP. 
  case:(BR_di_pos_neg yps); apply / rge0xP /BR_gleP /sb /Zo_i => //; try ue.
  rewrite ww xnz; exact(rleR RS0).
have xps: inc x BRps by apply /BRps_iP.
have he:= continuous_square yr.
case: (rleT_ell xr ysr) => // le.
  move /(rlt_diffP xr ysr): (le) => ep; move:(he _ ep) => [d dp de].
  have dr :=  (BRps_sBR dp).
  case: (rleT_el yr dr) => le2.
    have ne1: BR_near y d \0r. 
    hnf;rewrite (BRdiff_0r yr); split; [ exact:RS0 | by rewrite BRabs_pos].
    move: (proj2(de _ ne1)); rewrite /BR_near /BRsquare BRprod_0r.
    rewrite (BRdiff_0r ysr) (BRabs_pos ysp) => /(BRdiff_le2P ysr xr ysr).
    by rewrite (BRdiff_xx ysr) => / rge0xP hi; case:(BR_di_pos_neg xps). 
  have le3: inc (y -r d) BRp by apply/(rle_diffP dr yr); BRo_tac.
  have le4': y -r d <r y. 
    by apply /(BRdiff_lt1P yr dr yr); rewrite (BRdiff_xx yr);apply/ rlt0xP.
  have le4:= (proj1 le4'). 
  have dp':= (BRps_sBRp dp).
  have ne1: BR_near y d (y -r d).  
    split => //; first by BRo_tac. 
    rewrite (BRdiff_diff_simp yr dr) (BRabs_pos dp'); exact: rleR.
  have le5:= (BRsquare_mon1 le3 y0 le4).
  have d1r:= (proj31 le5); move/(rle_diffP d1r ysr): le5 => le6.
  move: (de _ ne1) => [sd]; rewrite (BRabs_pos le6).
  move/(BRsum_le2l (RSo d1r) (RSo xr) ysr) =>/(rle_oppP xr d1r) => h.
  have: inc (y -r d) A by apply: Zo_i.
  move /sb /BR_gleP => hf; BRo_tac.
move /(rlt_diffP ysr xr): (le) => ep; move:(he _ ep) => [d dp de].
have dr := (BRps_sBR dp); have dr1 := (BRps_sBRp dp).
have ydr':= (RpS_sum y0 dr1).
have ydr:= (RSs yr dr). 
have le3':= (BRsum_Mps yr dp). 
case:(p_or_not_p  (y +r d <=r y));[ by move/ rleNgt | case; apply/BR_gleP/sc].
split => // => t /Zo_P[tp ta]; apply /BR_gleP /(BRsquare_mon2 ydr' tp).
have le4: BRabs d <=r d by rewrite (BRabs_pos dr1); apply:rleR.
have le1: inc (BRsquare (y +r d) -r BRsquare y) BRp.
  apply/(rle_diffP ysr (RSp ydr ydr));apply:(BRsquare_mon1 y0 ydr'(proj1 le3')).
have:(BR_near y d (y +r d)). 
 split; [exact | by rewrite (BRabs_diff yr ydr) (BRdiff_sum yr dr) ].
move/de => [se]; rewrite (BRabs_diff ysr se) (BRabs_pos le1).
move /(BRsum_le2r se xr (RSo ysr)) => sf; BRo_tac.
Qed.



Definition BRsqrt x := select (fun z => x = BRsquare z) BRp.

Lemma BRsqrt_prop x: inc x BRp ->
   x = BRsquare (BRsqrt x) /\ inc (BRsqrt x) BRp.
Proof.
move => h.
apply:(select_pr (BRsqrt_exists h) (BRsqrt_unique h)).
Qed.

Lemma sqrt2_prop : BRsqrt2 = BRsqrt \2r.
Proof. 
move: BRsqrt2_prop => [/BRps_sBRp sa sb].
move:(BRsqrt_prop (BRps_sBRp RpsS2)) => [sc sd].
exact: (BRsqrt_unique (BRps_sBRp RpsS2) sa (esym sb)  sd sc).
Qed.

(* Continuity and limit *)


Lemma limit_of_continuous xn x f (yn := Lg Nat (fun i => f (Vg xn i))):
   BR_seq xn -> continuous_at f x -> limitR xn x -> realp x ->
   (forall n, natp n -> inc  (f (Vg xn n)) BR) -> inc (f x) BR ->
   (BR_seq yn /\ limitR yn (f x)). 
Proof.
move => pa pd pe xr pf fxr.
have ha: BR_seq yn by apply:BR_seq_prop1.
split => // e ep.
move: (BQhalf_pos ep)(BQhalf_pos1 ep) => he le0.
move/(rlt_cQ (proj31_1 le0)  (proj32_1 le0)): le0 => le1.
move: (pd _ (RpsS_of_Q he)) => [e1 /BRcompare_zero [d dq dp] h].
move:(pe d dq) => [N NN h2]; exists N => // n nN le2.
move: (BR_seq_prop pa nN) (BR_seq_prop ha nN) (pf _ nN) => hb hd hf.
have hc: BR_near x e1 (Vg xn n). 
   split => //; rewrite BRabs_diff//; exact:(proj1 (rlt_ltT (h2 _ nN le2) dp)).
move: (proj2(h _ hc)); rewrite BRabs_diff // /yn LgV// => le3;
apply:(rle_ltT le3 le1).
Qed.

Lemma limit_of_continuous_prop xn x f:
   BR_seq xn -> continuous_at f x -> limitR xn x -> realp x ->
   exists2 N, natp N & forall n, natp n -> N <=c n -> realp (f (Vg xn n)). 
Proof.
move => ha pd pe xr.
move:(pd _ RpsS1) => [d /BRcompare_zero [d1 dq dp] h].
move:(pe _ dq) => [N NN Np]; exists N => // n na nb.
have xnn: realp (Vg xn n) by apply: BR_seq_prop.
move:(Np _ na nb)=> hh.
have:BR_near x d (Vg xn n). 
  split => //;  rewrite BRabs_diff //; exact (proj1(rlt_ltT hh dp)).
by move/h => [].
Qed.

Lemma limit_of_subset xn x n (yn:= Lg Nat (fun i => (Vg xn (n +c i)))):
   BR_seq xn -> limitR xn x -> natp n ->
   (BR_seq yn /\  limitR yn x). 
Proof.
move => pa pb nN.
have ha: BR_seq yn. 
  apply: BR_seq_prop1.
  by move => k  kn;apply: BR_seq_prop => //;apply:NS_sum.
split =>// e ep;move:(pb _ ep) => [N NN H]; exists N => // m mN le.
rewrite /yn LgV//; apply: H; fprops.
apply (cleT le); apply:csum_Mle0; fprops.
Qed.


Lemma limit_of_subset2 xn x n (yn:= Lg Nat (fun i => (Vg xn (n +c i)))):
   limitR yn x -> natp n -> limitR xn x.
Proof.
move => pa nN e ep.
move:(pa _ ep) => [N NN H]; exists (N +c n); fprops => m mN le.
have ha := (NS_diff n mN).
move: (Nsum_Mle0 N nN) => hb.
move:(cdiff_pr (cleT hb le)) => hc.
have hd: N <=c m -c n by apply:(csum_le2l nN NN ha); rewrite hc csumC.
by move: (H (m -c n) ha hd); rewrite /yn LgV// hc.
Qed.


Lemma limit_of_continuous2 xn x f 
   (coerce := fun z => Yo (realp z) z \0r)
   (yn := Lg Nat (fun i => coerce (f (Vg xn i)))):
   BR_seq xn -> continuous_at f x -> limitR xn x -> realp x-> inc (f x) BR ->
   (BR_seq yn /\ limitR yn (f x)). 
Proof.
move => xns fcx lix xr fxr.
have ha: BR_seq yn. 
   apply: BR_seq_prop1 => n nN; rewrite /coerce; Ytac h => //; apply:RS0.
split => //.
move:(limit_of_continuous_prop xns fcx lix xr)=> [N NN np].
move:(limit_of_subset xns lix NN) => []; set zn := Lg _ _ => zns limz.
have hb: forall n, natp n -> realp (f (Vg zn n)).
  move => n nN; rewrite /zn LgV//; apply: np; fprops;apply:csum_M0le; fprops.
move:(proj2 (limit_of_continuous zns fcx limz xr hb fxr)) => l1.
have l2:limitR (Lg Nat (fun i => Vg yn (N +c i))) (f x).
  move => e ep; move:(l1 _ ep) => [M Mn mp]; exists M => // n na nb.
  move:(NS_sum NN na) => sa;move: (mp _ na nb); rewrite /zn /yn ! LgV//. 
  by rewrite /coerce (Y_true (np (N +c n) sa (Nsum_M0le n NN))).
by apply:(limit_of_subset2 l2 NN).
Qed.

Lemma limit_of_continuous_fix x0 x f (seq:= induction_defined f x0)
      (xn := Lg Nat (Vf seq)):
   (forall x, realp x -> inc (f x) BR) -> inc x0 BR ->
   continuous_at f x -> limitR xn x -> realp x -> f x = x.
Proof.
move => ha x0r hb hc hd.
move: (induction_defined_pr f x0); rewrite -/seq; move => [qa qb qc qd].
have fgx: fgraph xn by rewrite /xn; fprops.
have dx: (domain xn) = Nat by rewrite  /xn Lgd.
have rb: forall n, natp n -> realp (Vg xn n).
  move => n nN; rewrite /xn LgV//; move: n nN; apply: Nat_induction; first ue.
  by move => n nN Hr; rewrite qd //; apply: ha.
have rc:(forall n : Set, natp n -> realp (f (Vg xn n))).
  by move => n nN; apply:ha;apply: rb.
have ra: BR_seq xn. 
  split => //t /(range_gP fgx) [n nd ->]; apply: rb; rewrite /natp; ue.
have rd: realp (f x) by apply: ha.
move: (proj2 (limit_of_continuous  ra hb hc hd rc rd)).
have ->:Lg Nat (fun i => f (Vg xn i)) = Lg Nat (fun i => Vg xn (\1c +c i)).
  apply:Lg_exten => // i iN; move:(NS_succ iN) => siN.
  by rewrite csumC - Nsucc_rw // /xn ! LgV//- qd.
move => l2; exact: (limitR_unique ra (ha _ hd) hd (limit_of_subset2 l2 NS1) hc).
Qed.

Lemma limit_positive xn x: 
   (forall n, natp n -> \0r <=r (Vg xn n)) ->
   BR_seq xn -> limitR xn x -> realp x -> \0r <=r x.
Proof.
move => pa pb pc xr; move/BR_i0P: (xr); case; last by move/ rle0xP.
move/BRopp_negative1 => ha;move/BRcompare_zero: (ha) => [e ea eb].
move/ (rlt_diffP2 (proj31_1 eb) (proj32_1 eb)): (eb).
rewrite /BRdiff; rewrite (BRopp_K xr) => / rgt0xP pec.
move:(pc _ ea) => [n nN h].
move / rle0xP:(pa _ nN) => ed.
have pd: inc (Vg xn n -r x)  BRp by apply: (RpS_sum ed (BRps_sBRp ha)).
move: (h _ nN (cleR (CS_nat nN))); rewrite (BRabs_pos pd) => ee.
move/(BRsum_lt2r (proj31_1 ee) (proj32_1 ee) xr): ee.
rewrite BRsumC (BRsum_diff xr (BRp_sBR ed)) => sa.
move:(rlt_ltT sa pec) => / rgt0xP /BR_di_neg_pos //.
Qed.


Lemma limit_of_continuous_fix_pos x0 x f (seq:= induction_defined f x0)
      (xn := Lg Nat (Vf seq)):
   (forall x, inc x BRp -> inc (f x) BRp) -> inc x0 BRp ->
   continuous_at f x -> limitR xn x -> realp x -> 
   f x = x /\ inc x BRp.
Proof.
move => pa pb pc pd pe.
move:(induction_defined_pr f x0); rewrite -/seq; move => [sa sb sc sd].
have spp: forall i, natp i -> inc (Vf seq i) BRp.
 by apply: Nat_induction; [ ue | move => n nN Hr; rewrite (sd _ nN); apply:pa].
have ha: forall n, natp n -> \0r <=r Vg xn n.
   by move => n nN; apply/ rle0xP; rewrite /xn LgV//; apply:spp.
have sxn: BR_seq xn by apply: BR_seq_prop1 => n /spp h; apply:BRp_sBR.
have xp:inc x BRp by apply/ rle0xP; apply: (limit_positive ha sxn pd pe).
have f0r:= (BRp_sBR (pa _ (RpS0))).
pose g z := Yo (inc z BRp) (f z) (f \0r).
have gp:(forall z, realp z -> realp (g z)).
   move => z zr; rewrite /g; Ytac h => //; exact (BRp_sBR(pa _ h)).
have eq1:(Lg Nat (Vf (induction_defined g x0))) = xn.
  move:(induction_defined_pr g x0) => [ua ub uc ud].
  apply:Lg_exten; apply: Nat_induction; first by rewrite uc sc.
  by move => n nN h;rewrite (ud _ nN) (sd _ nN) h /g (Y_true (spp _ nN)).
have gc: continuous_at g x.
  move => e ep; move:(pc _ ep) => [d dp dv]; exists d => // y yn.
  move:(dv _ yn)=>[su sv]; rewrite /BR_near /g (Y_true xp);Ytac h; first done.
  move: yn => [yr yn]; case/ (BR_i0P): yr => // ym.
  have oyp:= (BRopp_negative2 (BRms_sBRm ym)).
  have le1:= (BRsum_Mp pe oyp).
  suff aa: BR_near x d \0r by exact:(dv _ aa).
  split; [ apply: RS0| rewrite (BRdiff_0r pe) (BRabs_pos xp) ].
  move:yn; rewrite (BRabs_pos (RpS_sum xp oyp)) => le3; exact:(rleT le1 le3 ).
move:(limit_of_continuous_fix gp (BRp_sBR pb) gc); rewrite eq1 => hh.
by move:(hh pd pe); rewrite /g (Y_true xp) => ->.
Qed.


Lemma limit_of_continuous_fix_gea a x0 x f (seq:= induction_defined f x0)
      (xn := Lg Nat (Vf seq)):
   realp a ->
   (forall x, a <=r x -> a <=r (f x)) -> a <=r x0 ->
   continuous_at f x -> limitR xn x -> realp x -> 
   f x = x /\ a <=r x.
Proof.
move => h0 h1 h2 h3 h4 h5.
have eq0 := (BRsum_diff h0 h5).
have fxr :=(continuous_real h5 h3).
pose g x := f (a +r x) -r a.
set yn :=  Lg Nat (Vf (induction_defined g (x0 -r a))).
have eq1: (f x) -r a = g (x -r a) by rewrite /g eq0.
have k1:(forall t, inc t BRp -> inc (g t) BRp).
  move => t tp; move:(h1 _ (BRsum_Mp h0 tp)) => ra.
  by apply/(rle_diffP h0 (proj32 ra)).
have k2: inc (x0 -r a) BRp by apply/ (rle_diffP h0  (proj32 h2)).
have k3: continuous_at g (x -r a). 
  rewrite - eq0 in h3 fxr.
  have ra := (proj1 (continuous2_sum h0 (RS_diff h5 h0))).
  have rb :=(proj2 (continuous2_diff fxr h0)).
  exact:(continuous_comp ra (continuous_comp h3 rb)).
have k4: limitR yn (x -r a).
  have rb :=(proj2 (continuous2_diff h5 h0)).
  move: (induction_defined_pr f x0) => []; rewrite -/seq => sa sb sc sd.
  move: (induction_defined_pr g (x0 -r a)) => [sa' sb' sc' sd'].
  have a0: forall n, natp n ->  a <=r (Vf seq n).
    apply:Nat_induction; [ue | by move => n nN; rewrite (sd _ nN); apply: h1].
  have a1: forall n, natp n -> realp (Vf seq n) by move => n /a0 [].
  have a2: BR_seq xn by apply: BR_seq_prop1 => n /a1.
  have a3: forall n, natp n -> realp (Vg xn n -r a).
    move => n nN; rewrite /xn LgV//;apply: RS_diff => //; fprops.
  have ns0 := NS0.
  move:(proj2 (limit_of_continuous a2 rb h4 h5 a3 (RS_diff h5 h0))).
  congr(limitR _ (x -r a)); rewrite /xn/seq;apply: Lg_exten.
  apply: Nat_induction; first by rewrite LgV // sc sc'.
  move => n nN;move: (NS_succ nN) => snN; rewrite !LgV// => H.
  rewrite (sd _ nN) (sd' _ nN) - H /g BRsum_diff; fprops.  
have k5: inc (x -r a) BR by apply: RS_diff.
move:(limit_of_continuous_fix_pos k1 k2 k3 k4 k5).
rewrite /g (BRsum_diff h0 h5); move => [/(BRsum_eq2r fxr h5 (RSo h0)) ra].
by move /(rle_diffP h0 h5) => rb.
Qed.

Lemma decreasing_bounded_limit a xn (x := infimum BR_order (range xn)):
  BR_seq xn -> 
  (forall n, natp n -> a <=r (Vg xn n)) ->
  (forall n, natp n -> Vg xn (csucc n) <=r  Vg xn n) ->
  (a <=r x /\ limitR xn x).
Proof.
move => sa sb.
move: (sa) => [sc sd se sf].
have ar :=(proj31(sb _ NS0)).
move:BR_osr => [or sr].
have ha: sub (range xn) BR.
  move => t /(range_gP sc) [n na ->]; rewrite sd in na;exact:(proj32 (sb _ na)).
have ha': sub (range xn) (substrate BR_order) by rewrite sr.
have hb: nonempty (range xn).
  exists (Vg xn \0c); apply/(range_gP sc); rewrite sd. 
  by exists \0c => //; apply: NS0.
have hc: bounded_below BR_order (range xn).
  exists a; split; [ ue | move => y /(range_gP sc) [n na nb]]; apply /BR_gleP.
  by rewrite nb; apply:sb; rewrite /natp - sd.
move: (infimum_pr1 or (BR_inf_exists  ha hb hc)); rewrite -/x.
move/(glbP or ha'); rewrite /lower_bound sr; move =>[[hd he] hf].
have ax: a <=r x. 
  apply/BR_gleP; apply: hf; split => // y /(range_gP sc) [n na ->].
  by rewrite sd in na; apply/BR_gleP; apply:sb.
split; first exact.
have aux: forall n, natp n ->  BRabs (Vg xn n -r x) = (Vg xn n -r x).
  move => n nN. 
  have : inc (Vg xn n) (range xn) by apply/(range_gP sc); exists n => //; ue.
  move/he => /BR_gleP le1.
  by apply: BRabs_pos; apply / rle0xP/ (rle_diffP1 hd (proj32 le1)).
move => e ep. 
move:(RpsS_of_Q ep);set e' := BR_of_Q e => ep'.
case: (p_or_not_p (exists2 y,inc y (range xn) & y <r (x +r e'))); last first.
  move: (BRsum_Mps hd ep') => l1 ne.
  have H: forall y, inc y (range xn) -> gle BR_order (x +r e') y.
    move => y yr; ex_middle t; case: ne; exists y => //.
    have yrr: realp y by rewrite / realp - sr; apply: ha'.
    by case:(rleT_el (proj32_1 l1) yrr) => // /BR_gleP.
  move/hf: (conj (proj32_1 l1) H) => /BR_gleP l2; BRo_tac.
move => [y /(range_gP sc) [n nN ->] lt1].
rewrite sd in nN; exists n => // m mN lemn; rewrite (aux _ mN).
have le1: Vg xn m <=r Vg xn n. 
  rewrite - (cdiff_pr lemn);move: (m -c n)  (NS_diff n mN).
  apply:Nat_induction; first by rewrite (Nsum0r nN); apply: rleR; BRo_tac.
  by move => k kN /(rleT (sf _ (NS_sum nN kN))); rewrite (csum_nS _ kN). 
apply /(BRsum_lt2l (RS_diff (proj31 le1) hd) (BRps_sBR ep') hd).
rewrite (BRsum_diff hd (proj31 le1)); BRo_tac.
Qed.


Lemma increasing_bounded_limit a xn (x := supremum BR_order (range xn)):
  BR_seq xn -> 
  (forall n, natp n -> (Vg xn n) <=r a) ->
  (forall n, natp n -> (Vg xn n) <=r Vg xn (csucc n))  ->
  (x <=r a /\ limitR xn x).
Proof.
move: NS0 => ns0 ha hb hc.
set f:= Lg Nat (fun n => BRopp (Vg xn n)).
have ar :=(proj32 (hb _ NS0)).
set b := BRopp a.
have ra: BR_seq f by apply: BR_seq_prop1 => n nN;apply: RSo;apply: BR_seq_prop.
have hd: forall n, natp n ->  (Vg f n) = BRopp (Vg xn n).
  move => n nN; rewrite /f LgV//.
have rb: (forall n, natp n -> b <=r (Vg f n)).
  by move => n  nN; rewrite (hd _ nN); move:(hb _ nN); move/ rle_opp.
have rc: (forall n, natp n -> Vg f (csucc n) <=r  Vg f n).
  by move => n nN; rewrite (hd _ nN) (hd _ (NS_succ nN)); apply/ rle_opp /hc.
set y := infimum BR_order (range f).
move: (decreasing_bounded_limit ra rb rc);move => [rd re].
have yr: realp y by exact (proj32 rd).
have rf: (forall n, natp n -> inc (BRopp (Vg f n)) BR).
   by move => n / rb [_ fr _]; apply:RSo.
move: (ha) => [ha1 ha2 ha3].
have nre:  nonempty (range xn). 
  by exists (Vg xn \0c); apply/(range_gP ha1); rewrite ha2; exists \0c.
have rbb: (forall t, inc t (range xn) -> t <=r a).
  by move => t /(range_gP ha1); rewrite ha2; move => [n /hb ww ->].
have rg: xn = (Lg Nat (fun i => BRopp (Vg f i))).
rewrite /f;apply:fgraph_exten; fprops; aw;trivial;
  rewrite ha2 => u uN; rewrite !LgV//.
  by rewrite (BRopp_K (BR_seq_prop ha uN)).
have eq2: (fun_image (range xn) BRopp) = range f.
  move: ra => [ra1 ra2 ra3].
  set_extens t.
     move =>/funI_P [z /(range_gP ha1) [k kd ->] ->].
     apply /(range_gP ra1); rewrite / f; aw; exists k; first ue.
     rewrite LgV//; ue. 
  move/(range_gP ra1); rewrite ra2; move => [n nN ->]; rewrite /f LgV//.
  apply /funI_P;exists (Vg xn n)=> //;apply /(range_gP ha1); exists n=> //; ue.
move: (proj2(limit_of_continuous ra (continuous_opp yr) re yr rf (RSo yr))).
rewrite - (BRopp_K ar).
move: (BR_supremum_opp nre rbb); rewrite eq2 - rg -/x -/y => -> h.
by split => //; apply:rle_opp. 
Qed.


Lemma decreasing_limit_bounded_fix a x0 f
  (seq:= induction_defined f x0)  (xn := Lg Nat (Vf seq))
  (x := infimum BR_order (range xn)):
  (forall x, a <=r x ->  a <=r f x /\  f x <=r x) -> a <=r x0 ->
  (continuous_at f x) ->
  [/\ a <=r x, f x = x & limitR xn x].
Proof.
move => fp x0p fc. move: (proj31 x0p) => ar.
move:(induction_defined_pr f x0) => []; rewrite -/seq => ua ub uc ud.
have ha: forall n, natp n -> a <=r (Vf seq n). 
  apply: Nat_induction. ue. move => n nN H; rewrite (ud _ nN). 
  exact:(proj1 (fp _ H)).
have hb: (forall n, natp n -> a <=r (Vg xn n)).
  by move => n nN; rewrite /xn LgV//; apply: ha.
have hc: BR_seq xn by apply:BR_seq_prop1 => n /ha [].
have hd: (forall n, natp n -> Vg xn (csucc n) <=r  Vg xn n).
  move => n nN; move: (NS_succ nN) => snN;rewrite /xn !LgV// (ud _ nN).
  exact (proj2(fp _ (ha _ nN))).
have fp1: forall x, a <=r x -> a <=r f x by move => t /fp [].
move:(decreasing_bounded_limit hc hb hd) => [he hf]. 
move: (limit_of_continuous_fix_gea ar fp1 x0p fc hf (proj32 he)). 
by move => [sa sb]. 
Qed.



Lemma square_root_cv1 a b (f := fun z => (BRsquare z +r a) /r (\2r *r z))
  (seq:= induction_defined f b)  (xn := Lg Nat (Vf seq))
  (x := infimum BR_order (range xn)):
  inc a BRp -> \1r +r a <=r b ->
  [/\ inc x BRp, limitR xn x & BRsquare x = a].
Proof.
move => pa pb.
have ar: realp a by apply:BRp_sBR.
have tp2:=  (BRps_sBRp RpsS2).
move: (BRsqrt_exists pa) => [c cp cs].
have cr: realp c by apply:BRp_sBR.
have fz: f \0r = \0r by rewrite /f /BRdiv BRprod_0r BRinv_0  BRprod_0r.  
move: RS2 BR2_nz => rs2 r2z.
have cp1: forall t, c <=r t -> inc t BRp.
  move => t lt; apply / rle0xP; move/ rle0xP:  cp => sa;BRo_tac.
have cp2: forall t, c <=r t -> inc (\2r *r t) BRp.
   move => t /cp1 tr;apply  (RpS_prod tp2 tr). 
have comp_c: forall t, inc t BRp -> a <=r (BRsquare t) -> c <=r t.
  rewrite cs; move => t tp h; case: (rleT_el cr (BRp_sBR tp)) => // h2.
    move: (BRprod_Mltltge0 tp tp h2 h2) => h'; BRo_tac.
have nr: forall t, realp t -> inc (BRsquare t +r a) BRp. 
  move => t tr; exact (RpS_sum (RpS_square tr) pa).
have hc: forall t, c <=r t -> inc (BRsquare t -r a) BRp.
  move => t lct;  move: (proj32 lct) => tr.
  apply / rle0xP;apply/ (rle_diffP1 ar (RSp tr tr)); rewrite cs.
  apply: (BRprod_Mlelege0 (cp1 _ lct) cp lct lct).
have ha: forall t,inc t BR -> t -r (f t) = (BRsquare t -r a) /r (\2r *r t).
  move => t tr; case: (equal_or_not t \0r) => tnz.
    by rewrite tnz fz /BRdiv BRprod_0r BRinv_0  BRprod_0r (BRdiff_0r RS0).
  have pnz: \2r *r t <> \0r by apply: BRprod_nz.
  rewrite /f (BRdiff_div tr (BRp_sBR (nr _ tr)) (RSp RS2 tr) pnz).
  rewrite (BRprodC \2r) BRprodA // - (BRdouble_s (RSp tr tr)) (BRsumC _ a).
  by rewrite BRdiff_sum_simpl_r //; apply:RSp.
have hb: forall t, realp t -> inc (f t) BR.
  move => t tr; apply:(RS_div (BRp_sBR (nr _ tr))) (RSp rs2 tr).
rewrite /f /BRsquare.
have hd: forall t, c <=r t -> inc (f t) BRp.
  move => t ct;  apply: (RpS_div (nr _ (proj32 ct)) (cp2 _ ct)).
have he:(forall t, c <=r t -> f t <=r t).
  move => t lct; have tr:= (proj32 lct).
  apply/ (rle_diffP1 (hb _ tr) tr); rewrite (ha _ tr); apply/ rle0xP.
  apply /(RpS_div (hc _ lct) (cp2 _ lct)).
have hf:(forall t, c <=r t -> c <=r f t /\ f t <=r t).
  move => t lct; move:(proj32 lct) => tr; split; last by apply: he.
  apply: (comp_c _ (hd _ lct)).
  have str: realp (BRsquare t) by apply:RSp.
  have ra: realp (BRsquare t +r a) by apply:RSs.
  have rb:= (RSp RS2 tr).
  case: (equal_or_not t \0r) => tnz.
    move: lct cs; move/ rle0xP:cp;  rewrite tnz fz => sa sb. 
    rewrite (rleA sb sa) => ->; rewrite /BRsquare (BRprod_0r); BRo_tac.
  have rc: inc t BRps by apply/BRps_iP;move: (cp1 _ lct).
  set v := (BRsquare (BRsquare t +r a /r \1r)).
  have vv: v = (BRsquare (BRsquare t +r a)) by rewrite /v (BRdiv_x1 ar).
  have vr: realp v  by rewrite vv; apply:RSp.
  have rd:= (RpsS_prod RpsS2 rc).
  have re:=(RpsS_prod rd rd).
  rewrite /f (BRdiv_square ra rb) -(BRdiv_x1 ar).
  apply /(BRdiv_Mlelege0 ar RpsS1 vr re); rewrite (BRprod_1l vr) vv.
  rewrite (BRprod_ACA RS2 tr RS2 tr) (BRsumdiff_square (RSp tr tr) ar).
  rewrite BRprod_22 BRprodC -/(BRsquare t) (BRprodA RS4 str ar).
  exact (BRsum_Mp (RSp (RSp RS4 str) ar) (RpS_square (RS_diff str ar))).
have lcb: c <=r b.
  have bp1:= (rleT (BRsum_Mp RS1 pa) pb).
  have bp2 :=(BRps_sBRp RpsS1).
  move: (BRsum_Mp ar bp2); rewrite BRsumC=> bp3;move:(rleT bp3 pb) => bp4.
  have bp:inc b BRp by apply / rle0xP; move/ rle0xP: bp2 => h; BRo_tac.
  apply:comp_c => //.
  by move:(BRprod_Mlelege0  bp pa bp1 bp4);rewrite (BRprod_1l ar).
move: (induction_defined_pr f b) => []; rewrite -/seq => ua uvb uc ud.
have hi: BR_seq xn. 
   apply: BR_seq_prop1; apply: Nat_induction. 
      by rewrite uc; exact(proj32 lcb).
   by move => n nN h; rewrite ud //; apply: hb.
have hj: forall n, natp n -> c <=r Vg xn n /\ Vg xn (csucc n) <=r Vg xn n.
  move => n nN; move: (NS_succ nN) => snN;rewrite /xn !LgV//.
  clear snN; move: n nN; apply: Nat_induction.
    by rewrite (ud _ NS0) uc; split => //; apply: he.
  move => n nN [h1 h2]; move:(proj1 (hf _ h1)); rewrite - (ud _ nN) => h3.
  by split => //;rewrite (ud  _ (NS_succ nN)); apply: he.
have hk:(forall n, natp n -> c <=r Vg xn n) by move => t /hj [].
have hl:(forall n, natp n -> Vg xn (csucc n) <=r Vg xn n) by move => t /hj [].
move:(decreasing_bounded_limit  hi hk hl);rewrite -/x; move => [cxr lx].
clear hi hj hk hl.
case: (equal_or_not x \0r) => xnz.
  split => //; [by rewrite xnz; apply: RpS0 | rewrite cs xnz ].
  have -> //: c = \0r by apply:rleA; [ue | apply/ rle0xP].
move: (proj32 cxr) => xr.
have hg: f x = x -> BRsquare x = a.
  move => eq;move: (ha _ xr); rewrite eq (BRdiff_xx xr) => /esym h.
  case: (equal_or_not (BRsquare x -r a) \0r) => h1.
    by apply: (BRdiff_xx_rw (RSp xr xr) ar).
  have ra: realp (BRsquare x -r a) by apply: RS_diff => //; apply: RSp.
  have rb: realp (\2r *r x) by apply:RSp.
  have rc: (BRinv (\2r *r x)) <> \0r.
   by  move => /(BRinv_eq0 rb); apply: BRprod_nz.
  by case: (BRprod_nz ra (RS_inv rb) h1 rc).
have cfx: continuous_at f x.
  have p1: \2r *r x <> \0r by apply: BRprod_nz.
  have p2:=(continuous_prod xr (continuous_id  xr) (continuous_id  xr)).
  have ra := (proj2 (continuous2_sum (RSp xr xr) ar)).
  apply: (continuous_div xr p1 (continuous_comp p2 ra)).
  exact: (proj1(continuous2_prod RS2 xr)).
move:(decreasing_limit_bounded_fix hf lcb cfx) => [].
by rewrite -/seq -/xn -/x => Ra /hg Rb Rc; split => //; apply: cp1. 
Qed.


Lemma square_root_cv2 a (f := fun z => (BRsquare z +r a) /r (\2r *r z))
  (g := fun z => BRhalf ((f z) +r z)) (s := BRsqrt a):
  inc a BRp ->
  [/\ forall x,realp x -> x <> \0r -> (g x = x <-> x = s \/ x = BRopp s),
  (forall x, inc x BRp -> inc (g x) BRp),
  (forall x, \0r <=r x -> x <=r s -> x <=r (g x)) &
  (forall x, (s /r \3r) <=r x -> x <=r s -> g x <=r s)].
Proof.
move => pa; move: (BRp_sBR pa) => ra.
have fz: f \0r = \0r by rewrite /f /BRdiv BRprod_0r BRinv_0  BRprod_0r.  
move: RS2 BR2_nz (BRps_sBRp RpsS2) => rs2 r2z tp2.
have nr: forall t, realp t -> inc (BRsquare t +r a) BRp. 
  move => t tr; exact (RpS_sum (RpS_square tr) pa).
have ha: forall t, realp t -> t -r (f t) = (BRsquare t -r a) /r (\2r *r t).
  move => t tr; case: (equal_or_not t \0r) => tnz.
    by rewrite tnz fz /BRdiv BRprod_0r BRinv_0  BRprod_0r (BRdiff_0r RS0).
  have pnz: \2r *r t <> \0r by apply: BRprod_nz.
  rewrite /f (BRdiff_div tr (BRp_sBR (nr _ tr)) (RSp RS2 tr) pnz).
  rewrite (BRprodC \2r) BRprodA // - (BRdouble_s (RSp tr tr)) (BRsumC _ a).
  by rewrite BRdiff_sum_simpl_r //; apply:RSp.
have hb: forall t, realp t -> realp (f t).
  move => t tr; apply:(RS_div (BRp_sBR(nr _ tr)) (RSp rs2 tr)).
have hc: forall t, inc t BRp -> inc (f t) BRp. 
  move => t tp;  apply: (RpS_div (nr _ (BRp_sBR tp)) (RpS_prod tp2 tp)). 
have hd: forall t, inc t BRp -> inc (g t) BRp. 
  move => t tp; exact: (RpS_prod (RpS_sum (hc _ tp) tp) (BRps_sBRp RpsSh2)). 
have he: forall t, realp t -> realp (g t). 
   move => t tr; exact:(RSp (RSs (hb _ tr) tr) RSh2 ).
have hf: forall t, realp t -> t -r g t = BRhalf(t -r f t).
  move => t tr.
  rewrite /g BRhalf_prop (BRdiff_div tr (RSs (hb _ tr) tr) rs2 r2z).
  by rewrite -(BRdouble_s tr) (BRdiff_sum_simpl_r tr (hb _ tr) tr)  BRhalf_prop.
have hg: forall x, realp x -> (g x = x <-> x -r f x = \0r).
  move => x xr; split => h; move:(hf _ xr); rewrite h? (BRdiff_xx xr).
    move /esym/(BRprod_nz_bis  (RS_diff xr (hb _ xr))  RSh2); case => // h0.
    by case:(BRps_nz RpsSh2).
  by rewrite /BRhalf BRprod_0l; move/(BRdiff_xx_rw xr ((he _ xr))).
move: (BRsqrt_prop pa); rewrite -/s; move => [sa sb].
have sr := (BRp_sBR sb).
have hi:forall x, realp x -> x <> \0r -> (g x = x <-> x = s \/ x = BRopp s).
  move => x xr xnz; move:(hg _ xr); rewrite (ha _ xr) sa => ww.
  have qe: realp (BRsquare s) by apply:RSp.
  split.
    have qd:realp (BRsquare x) by apply:RSp.
    have qa:realp (BRsquare x -r BRsquare s) by apply:RS_diff.
    have qb:realp(BRinv (\2r *r x)) by apply:(RS_inv (RSp rs2 xr)).
    move/ww/(BRprod_nz_bis qa qb); case.
     by move/(BRdiff_xx_rw qd qe)/(BRsquare_inj xr (BRp_sBR sb)).
     move/(BRinv_eq0 (RSp rs2 xr))  /(BRprod_nz_bis RS2 xr); case => //.
   move/(BRsquare_inj xr sr ) => sx; apply /ww.
   by rewrite sx (BRdiff_xx qe) /BRdiv BRprod_0l.
have hj:forall x, \0r <=r x -> x <=r s -> x <=r g x.
  move => x / rle0xP xp le1; move:(BRp_sBR xp) => xr.
   apply /(rle_diffP2 xr (he _ xr)); rewrite (hf _ xr) /BRhalf BRprodC.
   apply:(RpmS_prod (BRps_sBRp RpsSh2)); rewrite (ha _ xr).
   apply:BRmpS_div (RpS_prod tp2 xp); rewrite sa (BRsquare_diff xr sr)  BRprodC.
   by apply:(RpmS_prod (RpS_sum xp sb)); apply /(rle_diffP2 xr sr).
split => //.
move => x le1 le2.
case: (equal_or_not s \0r) => snz.
  move:le1 le2; rewrite snz BRdiv_0x => le1 le2.
  rewrite /g /f (rleA le2 le1) (BRprod_0r) BRdiv_x0 (BRsum_0r RS0).
  rewrite /BRhalf(BRprod_0l); apply: (rleR RS0).
have spp: inc s BRps by apply/BRps_iP.
have xpp: inc x BRps. 
  apply/ rlt0xP; apply: rlt_leT le1; apply/ rlt0xP;exact:(RpsS_div spp RpsS3). 
have xnz:=(BRps_nz  xpp).
have xr: realp x by BRo_tac.
have pb: realp (BRsquare x) by apply:RSp.
have pc: realp (BRsquare x +r a) by apply:RSs.
have pd: realp (\2r *r x) by apply:RSp.
have pe: \2r *r x <> \0r by apply: BRprod_nz.
have ar := (BRp_sBR pa).
have pf:=(RSs (RSp RS3 pb) ar).
have gv: g x = (\3r *r BRsquare x +r a) /r (\4r *r x).
  rewrite /g/f BRsumC (BRsum_div xr pc pd pe) (BRprodC x) -(BRprodA RS2 xr xr).
  rewrite -/(BRsquare x) (BRsumA (RSp rs2 pb) pb ar).
  rewrite -{2} (BRprod_1l pb) - (BRprodDl pb rs2 RS1) BR_plus21 BRhalf_prop.
  rewrite /BRdiv - (BRprodA pf (RS_inv pd)(RS_inv rs2)) - (BRprod_inv pd rs2).
  rewrite(BRprodC _ \2r) (BRprodA rs2 rs2 xr) BRprod_22//.
have isr := proj32 le2.
have qa:= (RS_diff (RSp RS3 xr) isr).
have qb:= (RS_diff xr isr).
have qc':= (RpsS_prod RpsS4 xpp).
have qc:= (RSp RS4 xr).
have qd := RS_div (RSp qa qb) qc.
suff gv1: g x = s +r ((\3r *r  x -r s) *r ( x -r s)) /r (\4r *r x).
   rewrite gv1; apply: (BRsum_Mm isr); apply: BRmpS_div (BRps_sBRp qc').
   apply: RpmS_prod; last by apply/ rle_diffP2.
   move:(BRps_nz RpsS3) (BRps_sBRp RpsS3) => qe qf.
   rewrite - (BRprod_div RS3 sr qe) - (BRprodBr RS3 xr (RS_div sr RS3)). 
   by apply: (RpS_prod qf); apply/ (rle_diffP (proj31 le1) xr).
have rs3 := RS3.
have pxs := RSp xr sr.
move: (RSp RS3 pb)(RSp RS3 pxs)(RSp sr sr)(RSp RS4 pxs) => p3xx p3xs pss p4xs.
have qe: realp (\3r *r (x *r x) -r x *r s) by exact (RS_diff p3xx pxs).
rewrite (BRsum_div sr (RSp qa qb) qc (BRps_nz qc')) gv; congr (_ /r _).
rewrite sa (BRprodBr qa xr sr) (BRprodDl xr (RSp RS3 xr) (RSo sr)).
rewrite (BRprodDl sr (RSp RS3 xr) (RSo sr)) -! BRopp_prod_l  //.
rewrite  - (BRprodA rs3 xr xr)  - (BRprodA rs3 xr sr)  (BRprodC s x).
rewrite -/(_ -r _) (BRdiff_diff qe p3xs pss) (BRdiff_diff2 p3xx pxs p3xs).
rewrite -{1} (BRprod_1l pxs) - (BRprodDl pxs RS1 RS3) (BRsumC \1r)BR_plus31.
rewrite (BRprodC s) - (BRprodA RS4 xr sr).
by rewrite (BRsumA p4xs (RS_diff p3xx p4xs) pss) (BRsum_diff p4xs p3xx).
Qed.


Lemma square_root_cv3 a b (f := fun z => (BRsquare z +r a) /r (\2r *r z))
  (g := fun z => BRhalf ((f z) +r z)) (s := BRsqrt a)
  (seq:= induction_defined g b)  (xn := Lg Nat (Vf seq))
  (x := supremum BR_order (range xn)):
  inc a BRp ->  (s /r \3r) <=r b -> b <=r s ->
  [/\ inc x BRp, limitR xn x & x = s]. 
Proof.
move => pa pb pc.
move:(square_root_cv2 pa) => [ha hb hc hd].
move: (BRsqrt_prop pa); rewrite -/s; move => [sa sb].
have sp: \0r <=r  s /r \3r by apply/ rle0xP;exact(RpS_div sb (BRps_sBRp RpsS3)).
have srr := (BRp_sBR sb).
have bp: inc b BRp by apply / rle0xP; BRo_tac.
set B := Zo BR (fun z =>  s /r \3r <=r z /\ z <=r s).
have bb: inc b B by apply:Zo_i; [ apply:BRp_sBR |  done ].
have Bp: forall z, inc z B -> inc (g z) B.
  move => z /Zo_P [szr [za zb]]; move:(hd _ za zb) => zc.
  move:(rleT za (hc _ (rleT sp za) zb)) => sd. 
  apply: Zo_i => //; exact:(proj32 sd).
move: (induction_defined_pr g b) => []; rewrite -/seq => ua ub uc ud.
have qa: fgraph xn by rewrite /xn; fprops. 
have qb: domain xn = Nat by rewrite /xn;aw.
have srb: sub (range xn) B.
  move => t /(range_gP qa); rewrite qb; move => [n nN ->]; rewrite /xn LgV//.
  move: n nN ; apply: Nat_induction; first ue.
  by move => n nN h; rewrite (ud _ nN); apply: Bp.
have he: sub (range xn) BR by move => t /srb /Zo_S.
have Vseq: forall n, natp n -> Vg xn n = Vf seq n.   
  move => n nN; rewrite /xn LgV//.
have seqz: forall n, natp n -> inc  (Vg xn n) B.
   move => n nN; apply: srb;apply/(range_gP qa);rewrite qb; exists n; fprops.
have seqx: BR_seq xn by split.
have seqy:forall n, natp n -> Vg xn n <=r s by move  => n  /seqz /Zo_P [_ []].
have seqt: (forall n, natp n -> Vg xn n <=r Vg xn (csucc n)). 
  move => n nN; move: (seqz  _ nN) => /Zo_hi []. 
  rewrite (Vseq _ nN) (Vseq _ (NS_succ nN)) (ud _ nN) => p1 p2.
  apply: hc => //; BRo_tac.
move:(increasing_bounded_limit seqx seqy seqt) => [];rewrite -/x => Ha Hb.
move:BR_osr => [or sr].
have he': sub (range xn) (substrate BR_order) by rewrite sr.
have hf': inc (Vg xn \0c) (range xn).
  by apply/(range_gP qa); rewrite qb; exists \0c => //; apply: NS0.
have hf: nonempty (range xn) by ex_tac.
have hg: bounded_above BR_order (range xn).
  by exists s; split; [ue | move => y /srb /Zo_hi [_] /BR_gleP].
move: (supremum_pr1 or (BR_sup_exists  he hf hg)); rewrite -/x.
move/(lubP or he');rewrite /upper_bound sr;move=> [[xr hj] hk].
have hl': (Vg xn \0c) = b by rewrite /xn LgV//; apply: NS0.
have hl: s /r \3r <=r x by apply /(rleT pb)  /BR_gleP / hj; rewrite - hl'.
have xp: inc x BRp by apply / rle0xP;exact: (rleT sp hl).
case: (equal_or_not x \0r) => xnz.
  rewrite xnz in hl;  move:(rleA hl sp) => /(BRprod_nz_bis srr (RS_inv RS3)).
  case; first by move => ->;split => //; rewrite xnz; apply:RpS0.
  by move/(BRinv_eq0 RS3) => h; case: (BRps_nz RpsS3).
have xpp: inc x BRps by apply setC1_P.
move: RS2 BR2_nz (BRps_sBRp RpsS2) => rs2 r2z tp2.
have cfx: continuous_at f x.
  have p1: \2r *r x <> \0r by apply: BRprod_nz.
  have p2:=(continuous_prod xr (continuous_id  xr) (continuous_id  xr)).
  have ra := (proj2 (continuous2_sum (RSp xr xr) (BRp_sBR pa))).
  apply: (continuous_div xr p1 (continuous_comp p2 ra)).
  exact: (proj1(continuous2_prod RS2 xr)).
have cgx: continuous_at g x.
  have p2:= (continuous_sum xr cfx (continuous_id  xr)).
  have p3:= (RS_div (RSs (RSp xr xr) (BRp_sBR pa)) (RSp rs2 xr)).
  exact:(continuous_comp p2 (proj2(continuous2_prod (RSs p3 xr) RSh2))).
move: (limit_of_continuous_fix_pos hb bp cgx Hb xr) => [ea eb].
move:(proj1 (ha _ xr xnz) ea); case => xs; first done.
case: (BR_di_pos_neg xpp); rewrite xs; exact: (BRopp_positive2 sb). 
Qed.

Section FinitePower.

Variable x: Set.
Hypothesis xr: realp x.

Definition BRnpow :=  induction_term (fun _ : Set => BRprod x) \1r.

Lemma BRnpowx0: BRnpow \0c = \1r.
Proof. apply: induction_term0. Qed.

Lemma BRnpowxS n : natp n -> BRnpow (csucc n) = x *r BRnpow n.
Proof. apply: induction_terms. Qed.

Lemma BRnpowx1: BRnpow \1c = x.
Proof. by rewrite - succ_zero (BRnpowxS NS0) BRnpowx0 (BRprod_1r). Qed.

Lemma RS_Brnpow n: natp n -> realp (BRnpow n).
Proof.
move:n; apply:Nat_induction; first by rewrite BRnpowx0; exact:RS1.
by move => n nN Hr; rewrite (BRnpowxS nN); apply: RSp.
Qed.

Lemma BRnpow_prop1 n m: natp n -> natp m ->
  (BRnpow n) *r (BRnpow m)  = (BRnpow (n +c m)).
Proof.
move => nN mN; move: n nN; apply: Nat_induction.
  by  rewrite  BRnpowx0 (csum0l (CS_nat mN)) (BRprod_1l (RS_Brnpow mN)).
move => n nN h.
rewrite (BRnpowxS nN) (csum_Sn _ nN)(BRnpowxS (NS_sum nN mN)) - h.
symmetry; apply: (BRprodA xr (RS_Brnpow nN) (RS_Brnpow mN)).
Qed.

End FinitePower.

Notation "x ^r y" := (BRnpow x y) (at level 30).

Lemma BRnpow00: \0r ^r \0c = \1r.
Proof. apply: BRnpowx0. Qed.

Lemma BRnpow0Sn n : natp n -> \0r ^r (csucc n) = \0r.
Proof. move => nN; rewrite  (BRnpowxS _ nN); apply: BRprod_0l. Qed.


Lemma BRnpow1n n : natp n -> \1r ^r n = \1r.
Proof.
move: n; apply: Nat_induction; first by rewrite  BRnpowx0.
  by move => n nN hr; rewrite (BRnpowxS _ nN) hr (BRprod_1l RS1).
Qed.


Lemma BRnpow_prop2 x y n : realp x -> realp y -> natp n ->
   (x*r y) ^r n =  x ^r n  *r y ^r n.
Proof.
move => xr yr.
move: n; apply: Nat_induction; first by rewrite  !BRnpowx0 (BRprod_1l RS1).
move => n nN hr.
by rewrite !(BRnpowxS _ nN) hr BRprod_ACA //; apply:RS_Brnpow.
Qed.




Definition BR_five := BR_of_Q (BQ_of_Z (BZ_of_nat \5c)).
Notation "\5r" := BR_five.


Lemma RpsS5 : inc \5r BRps.
Proof.
by apply: RpsS_of_Q; apply:BQ_of_Z_iQps;apply:BQpsS_fromN1; apply: NS4.
Qed.

Lemma RS5 : realp \5r.
Proof. apply:(BRps_sBR RpsS5). Qed.

Lemma BR_succ4 : \5r =  \4r +r \1r.
Proof.
rewrite(BRsum_cQ QS4 QS1) (BQsum_cZ ZS4 ZS1) (BZsum_cN NS4 NS1).
by rewrite - (Nsucc_rw NS4). 
Qed.

Definition BR_phi := BRhalf (\1r +r BRsqrt \5r).

Section Fibonacci.

Lemma fibr_prop1 a x y: realp x -> realp a -> realp y ->
   BRsquare y = a  -> x = (\1r +r y) /r \2r -> 
  BRsquare x = (a-r \1r)/r \4r +r x.
Proof.
move => xr ar yr syv ->.
have ha: realp (\1r +r y) by apply:(RSs RS1).
have hb:=(RSo RS1); have rs1 := RS1; have rs2 := RS2.
have hd: realp (a -r \1r) by apply: RS_diff.
rewrite (BRdiv_square ha RS2) (BRsum_square RS1 yr) syv {1}/BRsquare.
rewrite (BRprod_1l RS1) (BRprod_1l yr).
have ->: (\1r +r a) = (a -r \1r) +r BRdouble \1r.
  rewrite BRdouble_C - (BRdouble_s RS1) BRsumC BRsum_ACA // BRsum_opp_l //.
  by rewrite (BRsum_0r(RSs ar rs1)).
rewrite - (BRsumA hd (RSdouble rs1) (RSdouble yr)) /BRdouble - BRprodDr //.
rewrite (BRdiv_sumDl (RSp rs2 rs2) hd (RSp rs2 ha)) - BRprod_22.
rewrite BRdiv_prod_simpl_l//; exact: BR2_nz.
Qed.

Lemma fibr_prop2 x y: realp x -> realp y ->
   BRsquare y = \5r  -> x = (\1r +r y) /r \2r -> 
  BRsquare x = \1r +r x.
Proof.
move => xr yr ha hb.
rewrite (fibr_prop1 xr RS5 yr ha hb) BR_succ4 (BRdiff_sum1 RS1 RS4).
by rewrite (BRdiv_xx RS4) //; move/ rlt0xP: RpsS4 => [_ /nesym].
Qed.

Lemma BRps_phi: inc BR_phi BRps.
Proof.
move:(BRsqrt_prop (BRps_sBRp RpsS5)) => [ha hb].
apply:BRhalf_pos; rewrite BRsumC;exact :(RpsS_sum_r hb RpsS1).
Qed.

Lemma RS_phi: realp BR_phi.
Proof. exact (BRps_sBR BRps_phi). Qed.
  
Lemma fibr_prop3:  BRsquare BR_phi = \1r +r BR_phi.
Proof.
move:(BRsqrt_prop (BRps_sBRp RpsS5)) => [/esym ha hb].
apply:(fibr_prop2 (BRps_sBR BRps_phi) (BRp_sBR hb) ha); exact:BRhalf_prop.
Qed.

Lemma BRps_phii: inc (BRopp (BRinv BR_phi)) BRms.
Proof.
apply: BRopp_positive1; apply:RpsS_inv BRps_phi.
Qed.

Lemma fibr_prop4: BRinv BR_phi = BR_phi -r \1r.
Proof.
have ha:= (RS_inv RS_phi).
have hb:= (RS_diff RS_phi RS1).
have hc := (BRps_nz BRps_phi).
apply: (BRprod_eq2l ha hb RS_phi hc).
rewrite (BRprod_inv1 RS_phi hc)(BRprodBr RS_phi RS_phi RS1)(BRprod_1r RS_phi).
by rewrite  -/(BRsquare _)fibr_prop3 (BRdiff_sum1 RS_phi RS1). 
Qed.

Lemma fibr_prop5: BR_phi +r BRinv BR_phi = BRsqrt \5r.
Proof.
move:(BRsqrt_prop (BRps_sBRp RpsS5)) => [_ /BRp_sBR hu].
have ha := RS_phi.
have hb: realp (BRopp \1r) by apply: (RSo RS1).
have hc:= (RSs RS1 hu).
rewrite fibr_prop4 BRsumA // /BR_phi (BRdouble_half1 hc).
exact:(BRdiff_sum RS1 hu).
Qed.
  
Lemma fibr_prop6 (x := (BRopp (BRinv BR_phi))):  BRsquare x = \1r +r x.
Proof.
have ha:= (RS_inv RS_phi).
have hb:= (RS_diff RS1 ha).
have hc := (BRps_nz BRps_phi).
rewrite /x /BRsquare (BRprod_opp_opp ha ha) -/(_ -r _).
apply: (BRprod_eq2l (RSp ha ha) hb RS_phi hc).
rewrite (BRprodBr RS_phi RS1 ha) (BRprod_1r RS_phi).
rewrite  (BRprodA RS_phi ha ha) (BRprod_inv1 RS_phi hc) (BRprod_1l ha).
exact:fibr_prop4.
Qed.

Lemma fibr_prop7 x: realp x -> BRsquare x = \1r +r x ->
  forall n, natp n -> x ^r (csucc (csucc n)) = x ^r (csucc n) +r x ^r n.
Proof.
move => xr xrr n nN.
have xnr := (RS_Brnpow xr nN).
rewrite (BRnpowxS _ (NS_succ nN)) (BRnpowxS _ nN) BRprodA // -/(BRsquare _)xrr.
by rewrite BRsumC (BRprodDl xnr xr RS1) BRprod_1l.
Qed.

Theorem  fibr_prop8
  (fr := fun n => (BR_phi ^r n -r ((BRopp (BRinv BR_phi)))^r n)/r (BRsqrt \5r)):
  forall n, natp n -> fr n = BR_of_Q (BQ_of_Z (BZ_of_nat (Fib n))) .
Proof.
pose ff := fun n => BR_of_Q (BQ_of_Z (BZ_of_nat (Fib n))).
suff: forall n, natp n -> fr n = ff n /\ fr (csucc n) = ff (csucc n).
  by move => H n nN; case: (H n nN).
have pa:= RS_phi.
have pb:realp (BRopp (BRinv BR_phi)) by apply:RSo; apply: RS_inv.
move:(BRsqrt_prop (BRps_sBRp RpsS5)) => [pc /BRp_sBR pd].
have pe:BRsqrt \5r <> \0r.
  by move => h; move:(BRps_nz RpsS5); rewrite pc h /BRsquare BRprod_0l.
apply: Nat_induction.
  rewrite /fr/ff succ_zero Fib0 Fib1 -/BR_zero -/BR_one BRnpowx0 (BRnpowx1 pa).
  rewrite BRnpowx0  (BRnpowx1 pb) (BRdiff_xx RS1) /BRdiff {1}/BRdiv.
  rewrite (BRopp_K (RS_inv pa)) fibr_prop5 BRdiv_xx // BRprod_0l //.
move => n nN [ha hb]; split => //.
have hc :=  (NS_succ nN);have hc' :=  (NS_succ hc).
have ->: ff (csucc (csucc n)) = fr n +r fr (csucc n).
  move:(NS_Fib nN) (NS_Fib hc) (NS_Fib hc') => qa qb qc.
  move:(BZ_of_nat_i qa)(BZ_of_nat_i qb) (BZ_of_nat_i qc) => ra rb rc.
  move:(BQ_of_Z_iQ ra)(BQ_of_Z_iQ rb) (BQ_of_Z_iQ rc) => sa sb sc.
  by rewrite ha hb /ff (Fib_rec nN) - BZsum_cN // - BQsum_cZ// BRsum_cQ //. 
move: fibr_prop3 fibr_prop6 => qa qb.
have qc: realp (BR_phi ^r n -r BRopp (BRinv BR_phi) ^r n).
  by apply: RS_diff;apply:RS_Brnpow.
have qd:realp (BR_phi ^r csucc n -r BRopp (BRinv BR_phi) ^r csucc n).
  by apply: RS_diff;apply:RS_Brnpow.
have qc':= (RS_Brnpow RS_phi hc).
have qd1':= (RS_Brnpow pb hc); have qd':= RSo qd1'.
have qd1'':= (RS_Brnpow pb nN); have qd'':= RSo qd1''.
have qc'':= (RS_Brnpow RS_phi nN).
rewrite/fr BRsumC - BRdiv_sumDl // /BRdiff BRsum_ACA // - BRoppD //.
by rewrite - (fibr_prop7 RS_phi qa nN) -(fibr_prop7 pb qb nN).
Qed.


End Fibonacci.
  

End RealNumbers.
Export RealNumbers.



