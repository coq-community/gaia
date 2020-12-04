(** * Theory of Sets : Ordinals
  Copyright INRIA (2009-2013) Apics; Marelle Team (Jose Grimm).
*)
(* $Id: sset12.v,v 1.4 2018/09/04 07:57:59 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Export sset11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals2.
  

(** ** Normal ordinal functional symbols *)


Definition ordinal_interval a b := Zo b (fun z => a <=o z).

Lemma ointvP b:
  ordinalp b -> forall a z,
  (inc z (ordinal_interval a b) <-> (a <=o z /\ z <o b)).
Proof.
move => ob a z; split.
  by move => /Zo_P [zb ab]; move:(proj32 ab) => oz;split => //; apply /oltP0. 
by move => [az] /oltP0 [pa pb pc]; apply: Zo_i.
Qed.

Lemma ointvP0 b: ordinalp b -> forall z,
  (inc z (ordinal_interval \0o b) <-> z <o b).
Proof.
move=> bb z; apply: (iff_trans (ointvP bb _ _ )).
split; first by case.
move=> h; split => //; exact: (ole0x (proj31_1 h)).
Qed.

Lemma ointv1 b: ordinalp b -> forall a,
  inc a (ordinal_interval \1o b) <-> (\0o <o a /\ a <o b).
Proof. 
move => ob a; split. 
  by move /(ointvP ob) => [/oge1P wp1 wp2]. 
by move => [/oge1P wp1 wp2]; apply /(ointvP ob).
Qed.

Lemma ointv_pr1 b: ordinalp b -> 
  ordinal_interval \0o b = b.
Proof.
move=> ob; set_extens t. 
  by move /(ointvP0 ob) /oltP0 => [ _ _].
by move => tb; move:(Os_ordinal ob tb) => ot;apply /(ointvP0 ob) /oltP0. 
Qed.

Lemma ointv_pr2 a b z:
  inc z (ordinal_interval a b) -> ordinalp z.
Proof. by move => /Zo_hi []. Qed. 

Lemma ointv_sup a b: a <o b -> 
  \osup (ordinal_interval a b) = \osup b.
Proof.
move => ab.
have [[oa ob _] _]:= ab; have laa:=(oleR oa).
have aux: sub (ordinal_interval a b) b.
  by move=> t /(ointvP ob) [_] / oltP0 [_ _].
have osb:= Os_ordinal ob.
apply: (ord_sup_1cofinal) => //; split => // u ub.
have ou:= (osb _ ub).
case: (oleT_ee oa ou) => aux1.
  exists u;  last exact (oleR ou).
  by apply /(ointvP ob);split => //; apply /oltP0.
by exists a => //; apply /(ointvP ob). 
Qed.

Lemma ointv_sup1 a b: a <o b -> limit_ordinal b ->
  \osup (ordinal_interval a b) = b.
Proof.
by move=> ab lb; rewrite (ointv_sup ab) - [LHS] (limit_nonsucc lb).
Qed.


Lemma least_ordinal5 x (p: property):
 \0o <o x -> ~(p x) ->
 let y := least_ordinal (fun z => (~ (\0o <o z -> p z))) x in
   [/\ ordinalp y, (\0o <o y), ~(p y) &
    (forall z, inc z (ordinal_interval \1o y) -> p z)].
Proof.
move=> ox px. 
have orx:= proj32_1 ox. 
pose q z :=  \0o <o z -> p z.
have nq: ~(q x) by  move => qx; move:(qx ox). 
move: (least_ordinal3 orx nq).
rewrite /= /q; set y := least_ordinal _ _. 
move=> [y1 y2 y3]; split => //; first by ex_middle h; case: y2. 
by move => z/(ointv1 y1) [z1 z2]; apply: y3.
Qed.


Definition ofs (f:fterm) := forall a, ordinalp a -> ordinalp (f a).
Definition ofsu (f:fterm) u := forall a, u <=o a -> ordinalp (f a).

Definition sincr_ofsu (f: fterm) u :=
  forall a b, u <=o a -> a <o b -> (f a) <o (f b).
Definition sincr_ofn f x := 
  forall a b, inc a x -> inc b x -> a <o b -> (Vf f a) <o (Vf f b).

Lemma ofs_sincru f u: sincr_ofsu f u -> ofsu f u.
Proof.
move=> pa x ux; exact: (proj31_1 (pa _ _ ux (oltS (proj32 ux)))).
Qed.


Lemma ofs_sincr f: sincr_ofs f -> ofs f.
Proof.
move=> pa x ox; exact: (proj31_1 (pa _ _  (oltS ox))).
Qed.

Lemma sincr_incr f: sincr_ofs f ->
   (forall a b, a <=o b -> f a <=o f b).
Proof.
move => h x y xy.
case:(ole_eqVlt xy) => exy; last by exact: (proj1 (h _ _ exy)).
rewrite - exy; exact (oleR (proj31_1 (h _ _  (oltS (proj31 xy))))).
Qed.

Lemma sincr_ofs_exten f1 f2:
  sincr_ofs f1 -> sincr_ofs f2 ->
  (forall x, ordinalp x -> exists2 y, ordinalp y & f1 x = f2 y) ->
  (forall x, ordinalp x -> exists2 y, ordinalp y & f2 x = f1 y) ->
  f1 =1o f2.
Proof.
move => i1 i2 rs1 rs2; apply: (least_ordinal2) => b ob pb.
move: (rs1 _ ob) => [a oa av]; rewrite av.
case (oleT_ell oa ob) => cab; first by rewrite cab.
  by move: (pb _ cab)(proj2 (i1  _ _ cab)); rewrite av.
move: (rs2 _ ob) => [c oc cv];rewrite cv.
case (oleT_ell oc ob)=> cbb;first by rewrite cbb.
  by move: (pb _ cbb) (proj2 (i2  _ _ cbb)); rewrite cv => ->.
by move: (i2 _ _ cab) (i1 _ _ cbb); rewrite av cv; move => h1 [/(oltNge h1)]. 
Qed.

Definition cont_ofn f x :=  
   (forall a, inc a x -> limit_ordinal a ->
      Vf f a = \osup (Vfs f a)).

Definition normal_function f x y:=
  [/\ function_prop f x y, sincr_ofn f x & cont_ofn f x].

Definition normal_ofs1 (f: fterm) u:= 
  sincr_ofsu f u /\
  (forall X, (forall x, inc x X -> u <=o x) -> nonempty X ->
    \osup (fun_image X f) = f (\osup X)). 


Definition normal_ofu_aux (f:fterm) u:= 
  forall a, limit_ordinal a -> u <o a -> 
    f a = \osup (fun_image (ordinal_interval u a) f).

Definition normal_ofs2 (f:fterm) u:= 
  sincr_ofsu f u /\ normal_ofu_aux f u.

Definition normal_of_aux (f:fterm) :=
  forall a, limit_ordinal a -> f a = \osup (fun_image a f).


Definition normal_ofs (f:fterm):= 
  sincr_ofs f /\  normal_of_aux f.

Lemma osum_normal a: ordinalp a -> normal_ofs (fun z => a +o z).
Proof.
move=> oa; split; first  by move=> x y xy; apply: osum_Meqlt. 
move=> b lb; move: (lb) => [ob iob olbp].
have op:= OS_sum2 oa ob.
have osE: ordinal_set (fun_image b (osum2 a)).
  apply: Os_funI => c /(Os_ordinal ob) oc; fprops.
apply:oleA; last first.
  apply:ord_ub_sup => // x /funI_P [z /(oltP ob) xx ->].
  exact: (proj1 (osum_Meqlt xx oa)).
split; [exact | by  apply:OS_sup | move => w].
rewrite (osum_rec_def oa ob) => h; apply /setU_P.
case /setU2_P:h.
  by move => wa; exists a => //; apply /funI_P;ex_tac; rewrite osum0r.
move /funI_P => [z za zb]; exists (osucc w); fprops.
have oz := (Os_ordinal ob za).
by apply /funI_P; exists (osucc z); [apply: olbp | rewrite zb - osum2_succ].
Qed.


Lemma oprod_normal a: \0o <o a -> normal_ofs (fun z => a *o z).
Proof.
move=> ap; split; first by move=> x y xy; apply: oprod_Meqlt.
have oa:= proj32_1 ap.
move=> b lb; move: (lb) => [ob iob olbp].
have op:= OS_prod2 oa ob.  
have osE: ordinal_set (fun_image b (oprod2 a)).
  apply:Os_funI => c /(Os_ordinal ob) oc; fprops.
apply:oleA; last first.
  apply:ord_ub_sup => // x /funI_P [z /(oltP ob) xx ->].
  by move: (proj1 (oprod_Meqlt xx ap)).
split; [exact | by  apply:OS_sup | move => w ].
rewrite (oprod_rec_def oa ob) => /funI_P [z /setX_P [z1 z2 z3] ->].
have z4:= (olbp _ z3).
have o3 := (Os_ordinal ob z3). 
have o4:= (Os_ordinal ob z4).
apply /setU_P; exists (a *o (osucc (Q z))).
  apply /(oltP (OS_prod2 oa o4)); rewrite (oprod2_succ oa o3).
  by apply: (osum_Meqlt _ (OS_prod2 oa o3)); apply/(oltP oa).
apply/funI_P; ex_tac.
Qed.


Lemma ord_sincr_cont_propu f u:
    (forall x, u <=o x -> f x <o f (osucc x)) ->
    normal_ofu_aux f u ->
    sincr_ofsu f u.
Proof.
move => h hc x y ux xy.
move: (proj32_1 xy) => oy. move: y oy xy; apply: least_ordinal2 => z sa sc.
case: (ordinal_limA sa). 
- move => -> ha; case: (olt0 ha).
- move=> [w ow wz]; rewrite wz; move /oltSleP => xw.
  have hx:= (h _ (oleT ux xw)).
  case: (equal_or_not x w); [by move => -> | move => xnw ].
  have: w <o z by rewrite wz;apply: oltS; apply: OS_succr; ue.
  move /sc => pw; exact: (olt_ltT (pw (conj xw xnw)) hx).
- move => lz xz.
  rewrite (hc z lz (ole_ltT ux xz)).
  move /limit_ordinal_P: lz => [ _ lz].
  have pa:= (lz _ xz); have psx:= (sc _ pa).
  have hb:= (oltS (proj32 ux)).
  move: (psx hb) => ha; apply:(olt_leT ha).
  set E := fun_image _ _.
  have: ordinal_set E. 
    apply:Os_funI => a /(ointvP sa) [ua az]; exact: (proj31_1 (h _ ua)).
  move /ord_sup_ub; apply; apply /funI_P; exists (osucc x) => //. 
  apply/ointvP => //; split  =>//;  apply: (oleT ux (proj1 hb)).
Qed.


Lemma ord_sincr_cont_prop f:
    (forall x, ordinalp x -> f x <o f (osucc x)) ->
    normal_of_aux f -> 
    sincr_ofs f.
Proof. 
move => pa pb.
have pa1: (forall x, \0o <=o x -> f x <o f (osucc x)).
  by move => x [_ ox _]; apply: pa.
have pa2: (forall x, limit_ordinal x ->
     \0o <o x -> f x = \osup (fun_image (ordinal_interval \0o x) f)).
  move => x lx; move: (lx) => /pb -> _; rewrite ointv_pr1 //;exact:(proj31 lx).
move => x y xy.
exact: (ord_sincr_cont_propu pa1 pa2 (ole0x (proj31_1 xy)) xy). 
Qed.

Lemma ord_sincr_cont_propv f x y: limit_ordinal x -> ordinalp y ->
    function_prop f x y ->
    (forall a, inc a x -> Vf f a <o Vf f (osucc a)) ->
    cont_ofn f x ->
    normal_function f x y.
Proof.
move => [ox _ lx] oy fpxy pa pb; split => // a b ax bx ab.
move: (proj32_1 ab) => ob; move: b ob ab bx; apply: least_ordinal2 => z sa sc.
case: (ordinal_limA sa).
- move => -> ha; case: (olt0 ha).
- move=> [w ow wz]; rewrite wz; move /oltSleP => xw zx.
  have wx: inc w x by apply: (ordinal_transitive ox zx); fprops.
  have hx:= pa _ wx.
  case: (equal_or_not a w); [by move => -> | move => xnw ].
  have: w <o z by rewrite wz;apply: oltS; apply: OS_succr; ue.
  move /sc => pw; exact: (olt_ltT  (pw (conj xw xnw) wx) hx).
- move => lz az zx; move: (lz) => [oz _ lz1].
  move: (proj31_1 az) => oa;move: (oltS oa) => soa.
  rewrite (pb z zx lz).
  move /limit_ordinal_P: lz=> [_ lz].
  move: (lz _ az) => pc; apply: (olt_leT (sc _ pc soa (lx _ ax))).  
  move: fpxy => [fx sf tf].
  have zz: sub z (source f) by rewrite sf; apply: (ordinal_transitive ox zx).
  apply:ord_sup_ub.
     move => t /(Vf_image_P fx zz) [u uz ->]. 
     apply: (Os_ordinal oy); rewrite - tf; Wtac.
  by apply /(Vf_image_P fx zz); exists (osucc a) => //; apply/(oltP oz).
Qed.


Lemma normal_ofs_equiv f u:
  normal_ofs1 f u <-> normal_ofs2 f u.
Proof.
rewrite /normal_ofs1/ normal_ofs2.
split; move=> [p2 p3]; split => //.
   move=> x lx ux.
   have [[ou ox _] _ ]:= ux; have uu := oleR ou.
   set X := (ordinal_interval u x).
   have p4: forall x, inc x X -> u <=o x by move=> y /(ointvP ox) [].
   have p5: nonempty X by exists u; apply /ointvP. 
   rewrite (p3 _ p4 p5 ) (ointv_sup1 ux lx) //.
move=> X Xp neX.
have p1:=(ofs_sincru p2).
set Y:= (fun_image X f).
have p4: ordinal_set Y by apply:Os_funI => z zX; apply: p1; apply: Xp.
have p7: ordinal_set X by move=>j /Xp[]. 
case: (inc_or_not (union X) X) => sX.
  have sf: inc (f (union X)) Y by apply /funI_P; ex_tac.
  have le1:= (ord_sup_ub p4 sf).
  have p5: ordinalp (f (union X)) by case: le1. 
  have p6:  (forall i, inc i Y -> i <=o (f (union X))).
    move=> i /funI_P [z zX ->].
    have h:= (ord_sup_ub p7 zX).
    case:(ole_eqVlt (ord_sup_ub p7 zX)). move ->;apply:oleR. fprops.
    by move => h2; case: (p2 _ _ (Xp _ zX) h2).
  exact:(oleA (ord_ub_sup p5 p6) le1).
case: (ord_sup_inVlimit p7 neX) => // ls.
have ltus: u <o \osup X.  
  move: (neX) => [x xX]; apply: (ole_ltT (Xp _ xX)).
  split; [ exact: (ord_sup_ub p7 xX) | dneg w; ue ].
rewrite (p3 _ ls ltus). 
have oos :=  (proj32_1 ltus).
have sXoi: sub X (ordinal_interval u (union X)).
  move=> t tX; apply /(ointvP oos).
  by split; [ apply: Xp | apply: ord_sup_sub].
set Z:= (fun_image _ f).
have sFxoi: sub (fun_image X f) Z by apply: funI_S.
have Zp: ordinal_set Z by apply:Os_funI => v /(ointvP oos) [uv _];apply: p1.
apply: (oleA  (ord_sup_M sFxoi Zp)).
apply: ord_ub_sup => //.
  by apply: OS_sup; move=> i ifi; apply: Zp; apply: sFxoi.
move=> i /funI_P [z /(ointvP oos) [uz zsX] ->].
move:(olt_sup p7 zsX) => [t tX zt].
apply:(oleT (proj1 (p2 _ _ uz zt ))).
apply: ord_sup_ub  => //; apply /funI_P; ex_tac. 
Qed.

Lemma normal_ofs_equiv1 f:
  normal_ofs1 f \0o <-> normal_ofs f.
Proof.
apply:(iff_trans (normal_ofs_equiv f _)).
split; move=> [h2 h3]; split => //.
- move=> x y xy; apply: h2=> //; apply: ole0x.
  by move: xy=> [[ox _ _] _].
- move=> x [pa pb pc].
  rewrite - {2} (ointv_pr1 pa).
  apply: h3 => //; apply /oltP0;split;fprops.
- by move=> x y r1 r2; apply: h2.
- move => x lx wnz.
  have [ox _ _] := lx.
  by rewrite (ointv_pr1 ox); apply: h3.
Qed.

Lemma normal_ofs_equiv2 f a:
  ordinalp a -> normal_ofs f -> normal_ofs1 f a.
Proof.
move=> oa; move /normal_ofs_equiv1 => [p2 p3]; split => //.
   move=> x y xp yp; apply: p2 =>//; apply: (ole0x (proj32 xp)).
move=> X xp xX; rewrite p3 //.
move=> t tx; exact: (ole0x (proj32 (xp _ tx))).
Qed.

Lemma normal_function_incr f a b:
  ordinalp a -> ordinalp b -> normal_function f a b ->
  (forall u v, u <=o v -> v <o a -> Vf f u <=o Vf f v).
Proof.
move => oa ob [[ff sf tf] pa pb] u v uv va.
have ua:=(ole_ltT uv va).
have iua: inc u a by apply/(oltP oa).
have iva: inc v a by apply/(oltP oa).
case:(ole_eqVlt uv)=> nuv; last by  case:(pa _ _ iua iva nuv).
have /(Os_ordinal ob) /oleR ov : inc (Vf f v) b by Wtac.
by rewrite nuv. 
Qed.

Lemma normal_function_equiv f a b X:
  ordinalp a -> ordinalp b -> normal_function f a b ->
  sub X a -> nonempty X ->
  (\osup X = a \/ Vf f (\osup X) = \osup (Vfs f X)).
Proof.
move => oa ob h.
have incf:= (normal_function_incr oa ob h).
move: h => [[ff sf tf] pa pb] Xa nex. 
have osx:= Os_sub (Os_ordinal oa) Xa.
set y := \osup X.
case: (equal_or_not y a) => eya; [by left | right].
have lya: y <o a by split => //; apply: ord_ub_sup => // x /Xa /(oltP oa) [].
have iya: inc y a by apply /(oltP oa).
have ofy: ordinalp (Vf f y) by apply: (Os_ordinal ob); Wtac.
have Xsf: sub X (source f) by ue.
have osi: ordinal_set (Vfs f X).
  move =>t /(Vf_image_P ff Xsf) [u uX ->];apply: (Os_ordinal ob); Wtac.
case: (inc_or_not y X) => iyX.
  apply: oleA; last first.
    apply:ord_ub_sup => // t /(Vf_image_P ff Xsf) [u uX ->].
    by apply: incf => //; apply: ord_sup_ub.
  apply:ord_sup_ub => //; apply /(Vf_image_P ff Xsf); ex_tac.
case: (ord_sup_inVlimit osx nex); rewrite -/y => // limy.
rewrite (pb _ iya limy).
have ysf: sub y (source f) by rewrite sf; move: lya => [[_ _ h] _].
have Xy: sub X y by move => t tX; case/oltP0:(ord_sup_sub osx iyX tX).
symmetry; apply: ord_sup_1cofinal; first split.
- move => t /(Vf_image_P ff Xsf) [u /Xy ux ->]; apply/(Vf_image_P ff ysf).
  ex_tac.
- move => t /(Vf_image_P ff ysf) [u /(oltP (proj31 limy)) uy ->].
  move: (olt_sup osx uy) => [z zx uz].
  have h: inc (Vf f z) (Vfs f X) by apply/(Vf_image_P ff Xsf); ex_tac.
  have /(oltP oa) za:= (Xa _ zx).
  ex_tac; apply: (incf _ _ (proj1 uz) za). 
- move =>t /(Vf_image_P ff ysf) [u uX ->];apply: (Os_ordinal ob); Wtac.
Qed.

Lemma normal_ofs_uniqueness1 f g (p:fterm) u:
   normal_ofs1 f u -> normal_ofs1 g u -> ordinalp u ->
   (forall x, u <=o x -> f (osucc x) = p (f x)) ->
   (forall x, u <=o x -> g (osucc x) = p (g x)) ->
   (f u = g u) ->
  (forall x, u <=o x -> f x = g x).
Proof.
move => [pa pb] [pc pd] ou pe pf pg x cp.
have ox:= proj32 cp. move: x ox cp. apply: least_ordinal2 => y p1 p3 yp.
case:(ole_eqVlt yp); [by move <- | move => uny].
case: (ordinal_limA p1).
- by move => y0; case: (@olt0 u); rewrite - y0.
- move => [t ot st]; rewrite st; rewrite st in p1.
  have h : u <=o t by apply /oltSleP; rewrite - st.
  move: (oltS (proj32 h)); rewrite - {1} st => ty.
  by rewrite (pe _ h) (pf _ h) (p3 _ ty h).
- move => ly.
  set E := ordinal_interval u y.
  have uu:=(oleR (proj31 yp)).
  have pe1: (forall x, inc x E -> u <=o x) by move => t/(ointvP p1) [].
  have pe2: nonempty E by exists u; apply /(ointvP p1).
  have pe3: \osup E = y by rewrite (ointv_sup1 uny ly).
  move: (pb _ pe1 pe2) (pd _ pe1 pe2); rewrite pe3 => <- <-.
  by apply:ord_sup_2funI => s /(ointvP p1) [s1 s2]; apply: p3.
Qed.

Lemma normal_ofs_uniqueness f g (p:fterm):
   normal_ofs f -> normal_ofs g -> 
   (forall x,  ordinalp x -> f (osucc x) = p (f x)) ->
   (forall x,  ordinalp x -> g (osucc x) = p (g x)) ->
  (f \0o = g \0o) ->
  f =1o g.
Proof.
move => pa pb pc pd pe y oy.
have pa':= (normal_ofs_equiv2 OS0 pa).
have pb':= (normal_ofs_equiv2 OS0 pb).
have pc':(forall x, \0o <=o x -> f (osucc x) = p (f x)). 
  by move => x xp; apply: pc (proj32 xp).
have pd':(forall x, \0o <=o x -> g (osucc x) = p (g x)). 
  move => x xp; apply: pd (proj32 xp).
apply:(normal_ofs_uniqueness1 pa' pb' OS0 pc' pd' pe); apply:(ole0x oy).
Qed.

Lemma normal_ofs_existence (p:fterm) a
  (osup := fun f => \osup (fun_image (domain f) (fun z => (p (Vg f z)))))
  (osupp:= fun f => Yo (domain f = \0o) a (osup f))
  (f:= transdef_ord osupp):
  (forall x, ordinalp x -> x <o p x) -> 
  (forall x y, x <=o y -> p x <=o p y) ->
  ordinalp a ->
  [/\ normal_ofs f, f \0o = a & 
   (forall x,  ordinalp x -> f (osucc x) = p (f x)) ].
Proof.
move => incrp pi oa.
have f0: f \0o = a.
  by rewrite /f(transdef_ord_pr osupp OS0) /osupp; aw; Ytac0.
have frec3 :forall y, \0o <o y -> f y = \osup (fun_image y (fun z => p (f z))).
  move => y [[_  oy _] ynz]; rewrite {1}/f (transdef_ord_pr osupp oy)/osupp.
  by rewrite -/f/osup; aw; Ytac0;  apply: ord_sup_2funI => t ty; rewrite LgV.
have frec4: forall x, ordinalp x -> ordinalp (f x).
  apply: least_ordinal2' => x ox hr.
  case: (ozero_dichot ox); first by move ->; ue.
  move/frec3 => ->; apply:OS_sup  => t /funI_P [z sa ->]. 
  exact:(proj32_1 (incrp _ (hr _ sa))).
have frec5: forall x y,  x <o y -> p (f x) <=o f y.
  move => x y xy.
  have oy:= (proj32_1 xy).
  have ixy:= (olt_i xy).
  have yp:= (ole_ltT (ole0x (proj31_1 xy)) xy).
  rewrite (frec3 _ yp); apply: ord_sup_ub;last by apply /funI_P; ex_tac.
  by move => t /funI_P [z /(Os_ordinal oy) /frec4 /incrp [[_ h _] _] ->]. 
have frec6: forall x y,  x <o y -> (f x) <o f y.
  move => x y xy; move: (frec5 _ _ xy) => l1.
  exact: (olt_leT (incrp _ (frec4 _ (proj31_1 xy))) l1). 
have frec7:forall x, ordinalp x -> f (osucc x) = p (f x).
  move => x ox.
  have xsx: x <o osucc x by apply: oltS.
  apply: oleA (frec5 _ _ xsx).
  have osx:= (OS_succ ox). 
  rewrite (frec3 _  (olt0S ox)) /osup;apply: ord_ub_sup.
  - by move:(incrp _ (frec4 _ ox)) => [[]].
  - move => t /funI_P [z zx ->]; apply: pi.
    case/setU1_P: zx; last by  move ->; exact: (oleR (frec4 _ ox)).
    by move /(oltP ox) => /frec6 [].
split => //; split =>// x lx; move:(proj31 lx) => ox.
rewrite (frec3 _ (limit_pos lx)).
have hz: forall z, inc z x -> z <o osucc z. 
  move => z zx ;apply: (oltS (Os_ordinal ox zx)). 
apply: ord_sup_2cofinal;split; move => c /funI_P [z zx ->]; move:(hz _ zx)=> ht.
  move:(proj33 lx _ zx) => h; exists (f (osucc z)); last by apply:frec5. 
  apply /funI_P; ex_tac.
exists (f (osucc z)); first by apply/funI_P; ex_tac; apply: frec7 (proj31_1 ht).
by case: (frec6 _ _ ht).
Qed.


Lemma normal_ofs_limit1 f u x: normal_ofs1 f u -> u <o x -> limit_ordinal x ->
  limit_ordinal (f x).
Proof.
move=> /normal_ofs_equiv [pa pb] cux lx. 
rewrite (pb _ lx cux); move/limit_ordinal_P: (lx) => [[[_ ox _] _] pd].
have ov := (ofs_sincru pa).
set E :=  (fun_image (ordinal_interval u x) f).
have ou:= proj31_1 cux; have luu:= (oleR ou).
have uu: inc u (ordinal_interval u x) by apply/(ointvP ox).
have oe: ordinal_set E. 
  by apply:Os_funI => z /(ointvP ox) [uz _]; apply: ov. 
have ne: nonempty E by rewrite /E;exists (f u); apply /funI_P;ex_tac.
case: (ord_sup_inVlimit oe ne) => //.
move=> /funI_P [z /(ointvP ox) [sa /pd sb] fz].
have lt1:= (oltS (proj32 sa)).
have se: inc (f (osucc z)) E.  
  apply /funI_P; exists (osucc z)=> //;apply /(ointvP ox).
  split => //;exact (oleT sa (proj1 lt1)). 
move: (ord_sup_ub oe se); rewrite fz => l1. 
case:(oltNge(pa z (osucc z) sa lt1) l1).
Qed.

Lemma normal_ofs_limit f x: normal_ofs f ->  limit_ordinal x ->
  limit_ordinal (f x).
Proof.
move => /(normal_ofs_equiv2 OS0) nf lx; apply:(normal_ofs_limit1 nf _ lx).
by apply: limit_pos.
Qed.

Lemma normal_ofs_compose1 f fb g gb: 
  ordinalp fb -> ordinalp  gb -> fb <=o g gb ->
  normal_ofs1 f fb -> normal_ofs1 g gb -> normal_ofs1 (f \o g) gb.
Proof.
move => ofb ogb le1 [sa pa] [sb pb]. 
have aux: forall z, gb <=o z -> fb <=o g z.
  move => z zh;  apply: (oleT le1).
  have oug:= (oleR (ofs_sincru sb zh)).
  case: (equal_or_not gb z); [move => -> // | move =>h].
  exact (proj1 (sb gb z (oleR ogb) (conj zh h))).
split.
  move => u v ha uv /=.
  by move: (sb _ _ ha uv); apply: sa; apply: aux.
move => X Xp neX /=; rewrite - (pb _ Xp neX).
set Y := (fun_image X g).
have sc:(forall x, inc x Y -> fb <=o x).
  by move => x /funI_P [z /Xp zx ->]; apply: aux.
have nY: nonempty Y by move: neX => [t tX]; exists (g t); apply /funI_P; ex_tac.
rewrite -(pa _ sc nY); congr union; set_extens t; move/funI_P => [z za ->].
  apply/funI_P; exists (g z)=> //;apply /funI_P; ex_tac.
move/funI_P: za => [u tX ->]; apply/funI_P; ex_tac.
Qed.

Lemma normal_ofs_compose f g: 
 normal_ofs f -> normal_ofs g -> normal_ofs (f \o g).
Proof.
move => /(normal_ofs_equiv2 OS0) pa /(normal_ofs_equiv2 OS0) pb.
have h := ole0x (ofs_sincru (proj1 pb) (oleR OS0)).
by move:(normal_ofs_compose1 OS0 OS0 h pa pb) => /normal_ofs_equiv1.
Qed.


Lemma osi_gex x f: sincr_ofs f -> ordinalp x -> x <=o (f x).
Proof.
move=> finc; move: x; apply: least_ordinal2 =>  x ox xp.
case: (oleT_el ox (ofs_sincr finc ox)) => // lt1. 
case: (oleNgt (xp _ lt1) (finc _ _ lt1)).
Qed.


Lemma normal_fn_unbounded f a x:
  normal_function f a a -> x<o a -> x <=o (Vf f x) /\ Vf f x <o a.
Proof.
move=> [[ff sf tf] finc _] laxx.
have [[ox oa _ ] _] := laxx.
move: x ox laxx; apply: least_ordinal2 => x ox xp lxa.
have xsf: inc x a by apply /(oltP oa).
have ft: inc (Vf f x) a by Wtac. 
have ft2: Vf f x <o a by apply/(oltP oa).
split => //; case: (oleT_el ox (proj31_1 ft2)) => // lt1.
case: (oleNgt (proj1 (xp (Vf f x) lt1 ft2)) (finc (Vf f x) x ft xsf lt1)).
Qed.

Lemma osi_gex1 x f:
   sincr_ofs f -> ordinalp x -> exists y,
      [/\ ordinalp y, x <=o (f y) &
        forall z, ordinalp z -> x <=o (f z) -> y <=o z].
Proof.
move=> finc ox.
have lxy:= (osi_gex finc ox).
pose p y := x <=o (f y).
have [pa pb pc]:= (@least_ordinal4 x p ox lxy).
by exists (least_ordinal p x). 
Qed.


Lemma osi_gexu f u t x:
  sincr_ofsu f u -> u <=o t -> t <=o f t -> t <=o x ->
   x <=o (f x).
Proof.
move=> finc ut tft tx.
have ox:=proj32 tx.
move: x ox tx; apply: least_ordinal2 => x ox xp ltx.
case: (oleT_el ox (ofs_sincru finc (oleT ut ltx))) => // lt1.
case:(ole_eqVlt ltx) => ty; first ue.
have pa:=(oleT tft (proj1 (finc t x ut ty))).
case: (oltNge (finc (f x)  x (oleT ut pa) lt1) (xp _ lt1 pa)).
Qed.


Lemma osum_limit x y: ordinalp x -> limit_ordinal y -> 
  limit_ordinal (x +o y).
Proof.
by move=> ox ly; apply:normal_ofs_limit=> //; apply: osum_normal. 
Qed.

Lemma oprod_limit x y: \0o <o x -> limit_ordinal y -> 
  limit_ordinal (x *o y).
Proof. by move=> ox ly; apply:normal_ofs_limit=> //; apply: oprod_normal. Qed.

(* noter *)
Lemma limit_nonsucc' a: limit_ordinal a -> osuccp a -> False.
Proof.
move => la osa.
move:(proj2(oltS (proj31 la))).
by rewrite -{1} (predo_K osa) - (limit_nonsucc la).
Qed.

Lemma osum_succP a b: ordinalp a -> ordinalp b ->
  (osuccp (a +o b) <-> ((b = \0c /\ osuccp a) \/ osuccp b)).
Proof.
move => oa ob; split.
  case :(ordinal_limA ob) => ov.
  - by rewrite ov (osum0r oa) => osa; left.
  - by right.
  - move => h; case:(limit_nonsucc' (osum_limit oa ov) h).
case; first by move => [-> osa]; rewrite (osum0r oa).
move => [c oc ->]; rewrite - (osum2_succ oa oc); exists (a+oc); fprops.
Qed.

  
Lemma oprod_succP a b: ordinalp a -> ordinalp b ->
  (osuccp  (a *o b) <-> osuccp a /\ osuccp b).
Proof.
move => oa ob.
split; last first.
  move => [osa [c oc ->]]; rewrite (oprod2_succ oa oc).
  by apply/(osum_succP (OS_prod2 oa oc) oa); right.
move => [c oc h].
case: (ordinal_limA oa).
- by move => az; move: h; rewrite az oprod0l // => /esym /osucc_nz.
- move => sa; split => //.
  have ap: \0o <o a by move: sa => [a' /olt0S oa' ->].
  case: (ordinal_limA ob).
  + by move => bz; move: h; rewrite bz oprod0r // => /esym /osucc_nz.
  + done. 
  + move => lb; move: (oprod_limit ap lb); rewrite h.
    by move/limit_ordinal_P => [ra rb]; case /oltSSP:(rb _ (oltS oc)).
- move => /limit_ordinal_P [ap la].
  move: (oquoremP oc ap) =>  [oq or cv rs].
  move:(osumA (OS_prod2 oa oq) or OS1). 
  rewrite - cv (osucc_pr or) (osucc_pr oc) => ha.
  move: (OS_succ oc) (OS_succ or)(la _ rs) => osc osr rs'.
  have d1:odiv_pr0 (osucc c) a (oquo c a) (osucc (orem c a)) by [].
  have d2: odiv_pr0 (osucc c) a b \0o.
    by split; fprops; rewrite (osum0r (OS_prod2 oa ob)) h.
  case:(osucc_nz (proj2(odivision_unique osc oa d1 d2))).
Qed.

Lemma odiff_normal a: ordinalp a -> normal_ofs1 (odiff ^~ a) a.
Proof.
move => oa; apply/normal_ofs_equiv.
have aux1:forall u v, a <=o u -> u <o v -> u -o a <o v -o a. 
  move => u v au uv; move: (oleT au (proj1 uv)) => av.
  move: (odiff_pr au) (odiff_pr av) => [ou e1] [ov e2].
  by move: uv; rewrite {1} e1 {1} e2; move /(osum_Meqltr ou ov oa).
have aux:forall u v, a <=o u -> u <=o v -> u -o a <=o v -o a. 
  move => u v au uv; move: (oleT au uv) => av.
  move: (odiff_pr au) (odiff_pr av) => [ou e1] [ov e2].
  by move: uv; rewrite {1} e1 {1} e2; move /(osum_Meqler ou ov oa).
split => // x lx ax.
have ox:= (proj31 lx).
set E := fun_image _ _.
have ose: ordinal_set E.
  by apply:Os_funI=> v /(ointvP ox) [[_ ov _] vx]; apply: OS_diff.
have m1: ordinal_ub E (x -o a).
  by move => t  /funI_P [v /(ointvP ox) [av [vx _]] -> ]; apply: aux.
have [sa sb]:= (odiff_pr (proj1 ax)).
have os:= (OS_sup ose).
have le1 := (ord_ub_sup sa m1).
case: (oleT_el sa os) => le2; first by apply:oleA.
move: (osum_Meqlt le2 oa); rewrite - sb => eq1.
have: inc (\osup E) E. 
  apply /funI_P;exists (a +o \osup E); last by symmetry; apply: odiff_pr1.
  by apply/(ointvP ox); split => //; apply:osum_Mle0.
move => /funI_P  [y /(ointvP ox) [e1 e2] eq].
move/(limit_ordinal_P): (lx) => [ _ h3]; move: (h3 _ e2) => h4.
have h5 :=(oltS (proj32 e1)).
have h6:= (aux1 _ _ e1 h5).
have se: (inc ((osucc y) -o a) E).
   apply/funI_P; exists (osucc y) => //; apply/(ointvP ox); split => //.
   exact: (oleT e1 (proj1 h5)). 
by move: (ord_sup_ub ose se); rewrite eq => /(oltNge h6).
Qed.

Lemma normal_shift f a: normal_ofs f -> ordinalp a ->
  normal_ofs (fun z => (f(a +o z) -o a)).
Proof.
move => sa oa.
have sb:= (normal_ofs_compose sa (osum_normal oa)).
have sc:= (odiff_normal oa).
set f1 := (odiff^~ a); set f2:= (f \o (osum2 a)).
have h1: a <=o f2 \0o.  
 rewrite /f2 /= (osum0r oa); exact: (osi_gex (proj1 sa) oa).
move/normal_ofs_equiv1: sb => sb'; apply/normal_ofs_equiv1.
exact:(normal_ofs_compose1 oa OS0 h1 sc sb'). 
Qed.

Lemma normal_ofs_existence1 (p:fterm) a u:
  (forall x, ordinalp x -> x <o p x) -> 
  (forall x y, x <=o y -> p x <=o p y) ->
  ordinalp a -> ordinalp u ->
  exists f, 
  [/\ normal_ofs1 f u, f u = a & 
   (forall x,  u <=o x -> f (osucc x) = p (f x)) ].
Proof.
move => ha hb oa ou.
move: (normal_ofs_existence ha hb oa).
set g := transdef_ord _; move => [ga gb gc].
have leuu:= oleR ou.
pose f x := g (x -o u); exists f; split; last first.
- move => x ux; move:(odiff_pr ux) =>[od dp].
  rewrite /f - (gc _ od). rewrite {1} dp.
  rewrite (osum2_succ) // odiff_pr1 //; apply:(OS_succ od).
- by rewrite - gb /f (odiff_wrong leuu).
  have ra:=(normal_ofs_equiv2 OS0 ga).
  have rb: \0c <=o u -o u by  rewrite (odiff_wrong leuu); apply: (oleR OS0).
  have rc := (odiff_normal ou).
  exact:(normal_ofs_compose1  (g:= (odiff^~ u) ) OS0 ou rb ra rc). 
Qed.

Lemma osum_increasing5 u f: ordinalp u ->
  (sincr_ofsu f u) ->
  ((forall x y, u <=o x -> ordinalp y -> f(x) +o y <=o f (x +o y))
  /\ (exists2 c, u <=o c & forall x, c <=o x -> x <=o f (x))).
Proof.
move=> ou h.
have osw:= (ofs_sincru h).
set goal1 := (forall x, _).
have pr1:goal1.
  move=> x y ux oy. 
  have ox:= proj32 ux.
  move: y oy; apply: least_ordinal2 => z oz hr.  
  have owx:= (osw _ ux).
  have pa t: ordinalp t -> u <=o (x +o t).
    move=>  ot;exact: (oleT ux (osum_Mle0 ox ot)). 
  have pb t: t <o z -> f x +o t <o f (x+o z). 
    move => ltz; apply: (ole_ltT (hr t ltz)).
    exact: (h _ _ (pa _ (proj31_1 ltz)) (osum_Meqlt ltz ox)).
  case: (ordinal_limA oz).
  - move=> ->; rewrite (osum0r ox)(osum0r owx); apply:(oleR owx).
  - move=> [t ot uv].
    move: (oltS ot); rewrite -uv => h1.
    rewrite {1} uv -(osum2_succ owx ot); apply /oleSltP; apply: (pb _ h1).
  - move: (osum_normal owx) => [_ opn].
    move=> lz; rewrite (opn _ lz).
    apply: ord_ub_sup; first by apply: osw; apply: pa.
    move=> i /funI_P[j jz ->].
    have ljz: j <o z by apply /oltP.
    exact:(proj1 (pb _ ljz)).
split; first by exact.
set b:= osucc u.
have ob: ordinalp b by apply: OS_succ.
move: (oltS ou); rewrite -/b; move => [leab _].
set c := b *o omega0.
have ab:= (oleT leab (oprod_Mle1 ob olt_0omega)).
exists c; first by exact.
suff bv: c <=o f c by move => x xc; apply: (osi_gexu h ab bv xc).
have bp: \0o <o b by apply: (olt0S ou).
have [_ aux] := (oprod_normal bp).
move: (aux _ omega_limit); rewrite - /c => e1; rewrite {1} e1.
have owc: ordinalp (f c) by apply:osw.
have H: forall z, inc z omega0 -> ordinalp (b *o z). 
   move => z zo;exact: (OS_prod2 ob  (OS_nat zo)).
apply: ord_ub_sup => // t /funI_P[z zo ->]; move:(H _ zo) => obz //.
have owb: ordinalp (f b) by apply: osw.
have oz := (OS_nat zo).
have le1: b *o z <=o (f b +o (b *o z)) by  apply: osum_M0le.
move: (pr1 _ _ leab obz);rewrite (oprod2_nsucc ob oz) => le2.
have le3:= (oleT le1 le2).
have ltno: (\1o +o z) <o omega0.
  apply: osum2_lt_omega; [apply :olt_1omega | by apply/(oltP OS_omega) ].
have le5: u <=o (b *o (\1o +o z)).
  by rewrite -(oprod2_nsucc ob oz); apply: (oleT leab); apply: osum_Mle0.
exact: (oleT le3(proj1 (h _ _ le5 (oprod_Meqlt ltno bp)))).
Qed.


Lemma normal_ofs_bounded x f: ordinalp x -> normal_ofs f ->
  x <o f \0o \/ exists y, [/\ ordinalp y, f y <=o x & x <o f (osucc y)].
Proof.
move=> ox [pa pb].
move: (osi_gex1 pa ox) => [y [oy xle ymin]].
case: (equal_or_not x (f y)) => xo.
  have lt1:= (pa _ _ (oltS oy)).
  rewrite xo;right; exists y; split => //; apply: (oleR (proj32 xle)).
have xlt: x <o f y by split.
case: (ordinal_limA oy).
    by move => ye; move: xlt; rewrite ye => xx; left.  
  move => [z oz yz]; rewrite yz in oy.
  right; exists z; rewrite -yz;split => //.
  move: (oltS oz); rewrite -yz => le3.
  move: (pa _ _ le3) => [[ofz _] _].
  case: (oleT_ee ofz ox) => //.
  move=> le1; case: (oleNgt (ymin _ oz le1) le3).
move => li; move: xlt; rewrite (pb _ li) => xu.
have os: ordinal_set (fun_image y f).
  apply:Os_funI => z /(Os_ordinal oy)  oz.
  exact: (ofs_sincr pa oz).
move: (olt_sup os xu) => [z /funI_P [t ty ->] le2].
have yt: t <o y by apply /(oltP oy).
case: (oleNgt (ymin _ (Os_ordinal oy ty) (proj1 le2)) yt).
Qed.

Definition least_fixedpoint_ge (f:fterm) x y:=
 [/\ x <=o y, f y = y & (forall z, x <=o z -> f z = z -> y <=o z)].
Definition the_least_fixedpoint_ge (f:fterm)  x := 
  (\osup (target (induction_defined f x))).

Definition fixpoints f := Zo (source f) (fun z => Vf f z = z).

Lemma normal_ofs_fix1 f u x:
  normal_ofs1 f u -> u <=o x -> x <=o f x ->
  least_fixedpoint_ge f x (the_least_fixedpoint_ge f x).
Proof.
move=> nf0 ux xfx; rewrite /the_least_fixedpoint_ge.
have ox:= proj31 xfx.
move: nf0 => [sif nf].
have aux: forall t, x <=o t -> t <=o f t. 
  by move => t; apply:(osi_gexu sif ux xfx).
move: (induction_defined_pr f x).
set g := induction_defined f x; move=> [sg sjg gz gnz].
have fg: function g by fct_tac.
set y := \osup (target g).
have pb: forall i, inc i (target g) -> x <=o i.
   move=> i itg; move: ((proj2 sjg) _  itg) => [j jsg ->].
   move: j jsg; rewrite sg; apply: Nat_induction.
     rewrite gz; apply: (oleR ox).
   move=> n nN; rewrite (gnz _ nN) => p1.
   exact: (oleT p1 (aux _ p1)). 
have pc: (forall i, inc i (target g) -> u <=o i).
   move=> i itg; exact: (oleT ux  (pb _ itg)).
have xi: inc x (target g) by rewrite -gz; Wtac; rewrite sg; apply:NS0.
have ne: nonempty (target g) by exists x.
have otg: ordinal_set (target g) by move=> t tg; case: (pb _ tg). 
split => //.
- exact:(ord_sup_ub otg xi).
- rewrite - (nf _ pc ne). 
  apply: ord_sup_1cofinal; [ split | done].
    move => t /funI_P [z ztg ->].
    move: ((proj2 sjg) _ ztg) => [i isg ->].
    by rewrite sg in isg; rewrite -gnz  //; Wtac;rewrite sg; apply:NS_succ.
  move=> a atg.
  move: ((proj2 sjg) _ atg) => [i isg ->].
  rewrite sg in isg. 
  have wt: inc (Vf g i) (target g) by Wtac. 
  exists (Vf g (csucc i)); rewrite (gnz _ isg).
     by apply /funI_P; exists (Vf g i).
  by apply: aux; apply: pb.
- move => z xz fz.
  have oz: ordinalp z by case:xz.
  apply: ord_ub_sup => //.
  move=> i itg; move: ((proj2 sjg) _  itg) => [j jsg ->].
  move: j jsg; rewrite sg; apply: Nat_induction; first by rewrite gz. 
  move=> n nN; rewrite (gnz _ nN) => p1.
  have /pc le1 : inc (Vf g n) (target g) by Wtac; ue.
  case: (equal_or_not (Vf g n) z) => h; first by rewrite h fz; apply:oleR.
  rewrite - fz; exact: (proj1 (sif _ _ le1 (conj p1 h))).
Qed.

Lemma normal_ofs_fix x f:
  normal_ofs f -> ordinalp x -> 
  least_fixedpoint_ge f x (the_least_fixedpoint_ge f x).
Proof.
move => nf ox.
move/normal_ofs_equiv1:(nf)=> nf1; apply: (normal_ofs_fix1 nf1 (ole0x ox)).
exact:(osi_gex (proj1 nf) ox).
Qed.

Lemma normal_function_fix f a x 
  (y:= the_least_fixedpoint_ge (Vf f) x): 
  normal_function f a a ->  x <o a ->
  (y = a \/
  [/\ x <=o y, y <o a, Vf f y = y & 
    (forall z, x <=o z -> z <o a -> Vf f z = z -> y <=o z)]).
Proof.
move=> nf lxa.
have  [[ox oa _] _] := lxa.
move:NS0 => ns0.
have aux: forall x, x <o a -> x <=o (Vf f x) /\ Vf f x <o a.
  by move => t ta; apply: normal_fn_unbounded.
move: (induction_defined_pr (Vf f) x).
set g := induction_defined (Vf f) x; move=> [sg sjg gz gnz].
have fg: function g by fct_tac.
move: (nf) => [[ff sf tf] sif nf0].
have pb: forall i, inc i (target g) -> x <=o i /\ i <o a.
   move=> i itg; move: ((proj2 sjg) _  itg) => [j jsg ->].
   move: j jsg; rewrite sg; apply: Nat_induction.
     rewrite gz; split => //; apply: (oleR ox).
   move=> n nN; rewrite (gnz _ nN); move => [p1 p2].
   move: (aux _ p2) => [s1 s2]; split => //; apply: (oleT p1 s1).
have osg: ordinal_set (target g) by move => i /pb [_][[]].
have sta: sub (target g) a by move => t /pb  [_] /(oltP oa).
have netg: nonempty (target g) by exists (Vf g \0c); Wtac; rewrite sg. 
have sa: x <=o y.
  by apply :ord_sup_ub => //; rewrite - /g - gz; Wtac; rewrite sg.
have sb: y <=o a by apply :ord_ub_sup => // i /pb [_ []].
case: (equal_or_not y a) => eya; [by left | right;split  => //; last first].
   move => z xz za fz.
   have oz:= proj32 xz.
   apply: ord_ub_sup => //.
   move=> i itg; move: ((proj2 sjg) _  itg) => [j jsg ->].
   move: j jsg; rewrite sg; apply: Nat_induction; first by rewrite gz. 
   move=> n nN; rewrite (gnz _ nN) => p1; rewrite - fz.
   case: (equal_or_not ( Vf g n) z) => neq; first by rewrite neq fz; apply:oleR.
   have ha: inc (Vf g n) a by apply /(oltP oa); apply: (ole_ltT p1 za).
   have hb: inc z a by apply/(oltP oa).
   exact (proj1(sif (Vf g n) z ha hb  (conj p1 neq))).
move: (aux _ (conj sb eya)) => [sc sd].
apply: oleA => //.
move: (sta); rewrite - sf => stf.
have ha: ordinal_set (Vfs f (target g)).
  by move => t /(Vf_image_P ff stf) [u /pb [_ /aux [_ [[oo _ _] _] ->]]].
case: (normal_function_equiv oa oa nf sta netg) => //; rewrite -/y => ->.
apply: ord_ub_sup => //; first by case:sa.
move => t /(Vf_image_P ff stf) [u utg ->].
move: (proj2 sjg _ utg)=> [v va ->].
rewrite  sg in va; rewrite  -  (gnz _ va); apply :ord_sup_ub => //.
by rewrite -/g; Wtac; rewrite sg; apply:NS_succ.
Qed.

Lemma next_fix_point_small f C (E:= cnext C): infinite_c C ->
  normal_ofs f ->
  (forall x, inc x E -> inc (f x) E) ->
  (forall x, inc x E -> inc (the_least_fixedpoint_ge f x) E).
Proof.
move => icE nf fee x xE.
have [pa pb pc] := (cnext_pr1 (proj1 icE)).
have [qa qb qc qd]:= (induction_defined_pr f x).
move: (image_smaller (proj1 qb));rewrite qa (surjective_pr0 qb)=> sa.
apply: cnext_sup => //.
  by apply: (cleT sa); rewrite cardinal_Nat; apply /infinite_c_P2.
move => t /(proj2 qb); rewrite qa; move => [z zN ->]; move: z zN.
apply: Nat_induction; [by ue | by move => n nN /fee hr; rewrite qd].
Qed.


Lemma next_fix_point_small1 f C x (E:= cnext C)
  (y:= the_least_fixedpoint_ge (Vf f) x): 
  infinite_c C -> normal_function f E E -> inc x E ->
   [/\ x <=o y, inc y E, Vf f y = y & 
    (forall z, x <=o z -> inc z E -> Vf f z = z -> y <=o z)].
Proof.
move => icE nf xE.
have  [pa pb pc]:= (cnext_pr1 (proj1 icE)).
have [qa qb qc qd] := (induction_defined_pr (Vf f) x).
move: (image_smaller (proj1 qb));rewrite qa (surjective_pr0 qb)=> sa.
have fee: (forall x, inc x E -> inc (Vf f x) E).
  move:nf => [[ff sf tf] pd pe].
  rewrite -{1} sf - tf => t tsf; Wtac.
have ye: inc y E.
  apply: cnext_sup => //.
    by apply: (cleT sa); rewrite cardinal_Nat; apply /infinite_c_P2.
  move => t /(proj2 qb); rewrite qa; move => [z zN ->]; move: z zN.
  apply: Nat_induction; first by rewrite qc.
  move => n nN /fee hr; rewrite qd //.
have [oe _] := (pa).
have xe: x <o E by apply/oltP. 
case: (normal_function_fix nf xe); rewrite -/y.
  by move => yee; move:ye; rewrite yee; move: (ordinal_irreflexive oe).
by move => [ta tb tc td]; split => // z xz ze; apply: td => //; apply/oltP.
Qed.

Lemma normal_fix_cofinal C (E := cnext C) f:
   infinite_c C -> normal_function f E E -> 
   ord_cofinal (fixpoints f) E.
Proof.
move => icE nf.
have [[ff sf tf] _ _] := nf.
split; first by rewrite - sf; apply: Zo_S.
move => x xE.
move: (next_fix_point_small1 icE nf xE); rewrite -/E - sf.
set y := the_least_fixedpoint_ge (Vf f) x; move => [pa pb pc pd].
by exists y => //; apply/Zo_P.
Qed.


Lemma normal_ofs_restriction f C (E := cnext C): 
  infinite_c  C-> normal_ofs f ->
  (forall x, inc x E -> inc (f x) E) -> 
  normal_function (Lf f E E) E E.
Proof.
move => ice [nfa nfb] Esf.
have ff: function (Lf f E E) by apply: lf_function.
have fp: function_prop (Lf f E E) E E by saw.
have si: sincr_ofn (Lf f E E) E by  move => a b aE bE /nfa; rewrite !LfV.
split => // a ae /nfb la; rewrite LfV // la; congr union.
have asE: sub a E.
   have oe: ordinalp E by exact : (proj1 (CS_cnext (proj1 ice))).
   move => t ta; exact:(ordinal_transitive oe ae ta).
have asf: sub a (source (Lf f E E)) by aw.
set_extens t.
  move/funI_P => [z za ->]; apply /(Vf_image_P ff asf);ex_tac.
  by rewrite LfV//;apply: asE.
move/(Vf_image_P ff asf) => [u ua]; move:(asE _ ua) => uE; aw => ->.
rewrite LfV//; apply /funI_P; ex_tac.
Qed.

Lemma big_ofs
  (p:= fun z => cnext (cardinal z))
  (osup := fun f => \osup (fun_image (domain f) (fun z => (p (Vg f z)))))
  (osupp:= fun f => Yo (domain f = \0o) \0o (osup f))
  (f:= transdef_ord osupp):
  [/\ normal_ofs f, f \0o = \0o,
   (forall x,  ordinalp x -> f (osucc x) = p (f x))&
   forall C, infinite_c C -> 
       exists x, inc x (cnext C) /\ ~ (inc (f x) (cnext C)) ].
Proof.
have sa: (forall x, ordinalp x -> x <o p x).
  move => x ox; rewrite /p.
  have pc: cardinalp (cardinal x) by fprops.
  have pa: cardinalp (cnext (cardinal x)) by apply: CS_cnext. 
  apply /(oltP (proj1 pa)); apply /(cnextP pc); split; fprops.
have sb: (forall x y, x <=o y -> p x <=o p y).
  move => x y xy; rewrite /p.
  have h := (ocle1 xy).
  by apply:ocle; apply:cnext_pr6.
move: (normal_ofs_existence sa sb OS0).
rewrite -/osup -/osupp -/f.
move => [pa pb pc]; split => //.
move => c ic; exists (osucc c).
have cc:= (proj1 ic).
have oc:= (proj1 cc).
have cs:= (CS_cnext cc).
have oso:=(OS_succ oc).
split. 
   have os1 := OS1.
   apply /(cnextP cc); split => //.
   rewrite - osucc_pr // osum_cardinal // (card_card cc) csum_inf //.
     fprops.
   rewrite (card_card CS1); apply: cle_fin_inf; fprops.
have eq1: (f (osucc c)) = p (f c) by apply: pc.
move /(cnextP cc)=> [sc sd].
have se: c <=o (f c) by apply: (osi_gex (proj1 pa) oc).
have: p c <=o p (f c) by apply: sb.
move /ocle1; rewrite - eq1 /p (card_card cc).
rewrite (card_card cs) => h.
exact: (cleNgt (cleT h sd) (cnext_pr2 cc)). 
Qed.


Lemma omax_p2 y (c:= cardinal (omax y omega0)):
    ordinalp y -> (infinite_c c /\ inc y (cnext c)).
Proof.
move:OS_omega => oo oy; move:(omax_p1 oy oo) => [pa pb]; split.
  by apply /infinite_c_P2; move: (ocle1 pb); rewrite cardinal_Nat.
by apply /cnextP; [ rewrite /c; fprops | split=> //; apply: ocle1 ].
Qed.

Lemma omax_p3 x y (c:= cardinal (omax (omax x y) omega0)):
   ordinalp x ->  ordinalp y ->
   [/\ infinite_c c, inc x (cnext c) & inc y (cnext c)].
Proof.
move => ox oy.
move:(omax_p2 (OS_omax ox oy)); rewrite -/c; move => [ca cb].
move: (omax_p1 ox oy) => [ta tb].
have aux: forall t, t <=o omax x y -> inc t (cnext c).
   move: (proj1 (CS_cnext (proj1 ca))) => oc.
   have od: (omax x y) <o (cnext c) by apply  /(oltP oc).
   by move => t tc; apply /(oltP oc); apply: (ole_ltT tc od).
by split => //; apply: aux.
Qed.

Definition card_max x y:= cardinal (omax (omax x y) omega0).

Lemma ofs_add_restr a y (c:= card_max a y) (E := cnext c)
  (f:= Lf (fun z => a +o z) E E) :
  ordinalp a -> ordinalp y ->
  [/\ (forall x, inc x E -> inc (a +o x) E ),
      (forall x, x <=o y -> inc x E),
      normal_function f E E &
      forall x, inc x E -> Vf f x = a +o x].
Proof.
move => oa oy.
move: (omax_p3 oa oy); rewrite -/(card_max _ _) -/c -/E.
move => [icc ae ye].
have pa: forall x, x <=o y -> inc x E.
   have oc:= (proj1 (CS_cnext (proj1 icc))).
   have yc:y <o cnext c by apply/(oltP oc).
   move => x xe; apply/(oltP oc); apply:(ole_ltT xe yc).
have pb: forall x, inc x E -> inc (a +o x) E. 
   by move => x xe;apply: cnext_sum.
move: (normal_ofs_restriction icc (osum_normal oa) pb) => pc.
by split => //x xe; rewrite /f LfV.
Qed.

Lemma ofs_mul_restr a y (c:= card_max a y) (E := cnext c)
  (f:= Lf (fun z => a *o z) E E) :
  \0o <o a -> ordinalp y ->
  [/\ (forall x, inc x E -> inc (a *o x) E ),
      (forall x, x <=o y -> inc x E),
      normal_function f E E &
      forall x, inc x E -> Vf f x = a *o x].
Proof.
move => ap oy.
have oa:= (proj32_1 ap).
move: (omax_p3 oa oy); rewrite -/(card_max _ _) -/c -/E.
move => [icc ae ye].
have pa: forall x, x <=o y -> inc x E.
   have oc:=(proj1 (CS_cnext (proj1 icc))).
   have yc:y <o cnext c by apply/(oltP oc).
   move => x xe; apply/(oltP oc); apply: (ole_ltT xe yc).
have pb: forall x, inc x E -> inc (a *o x) E. 
   by move => x xe;apply: cnext_prod.
have pc:= (normal_ofs_restriction icc (oprod_normal ap) pb).
by split => //x xe; rewrite /f LfV.
Qed.

(* unbounded_non_coll *)


Definition ordinal_prop (p:property) := forall x, p x -> ordinalp x.

Definition iclosed_set E :=
   (ordinal_set E) /\
   (forall F, sub F E -> nonempty F -> (\osup F = \osup E \/ inc (\osup F) E)).
Definition iclosed_collection (E:property) :=
   ordinal_prop E /\
   (forall F, (forall x, inc x F -> E x) ->  nonempty F -> E (\osup F)).
Definition iclosed_proper (E:property) :=
  iclosed_collection  E /\ non_coll E.


Lemma iclosed_ord x: ordinalp x -> iclosed_set x.
Proof.
move => ox. 
have osx:= Os_ordinal ox.
split => // F fo _.
have h:= (ord_ub_sup1 ox fo).
case:(ole_eqVlt h) => e1; last by right;apply /(oltP ox).
left; apply: (ord_sup_1cofinal _ osx); split => //  a ax.
have au: a <o union F by rewrite e1; apply /oltP.
move:(@olt_sup F a (Os_sub osx fo) au)=> [z za [zb _]]; ex_tac.
Qed.


Lemma iclosed_lim: iclosed_proper limit_ordinal.
Proof.
split; last first.
  apply:unbounded_non_coll => x ox; exists (x +o omega0).
    exact: (osum_Mle0 ox OS_omega).
  exact:(osum_limit ox omega_limit ).
split; first by move => x [].
move => F fl nef.
have os: ordinal_set F by move => x /fl [].
case: (ord_sup_inVlimit os nef); [ by move /fl | done].
Qed.

Lemma iclosed_nonlim:
   ~(iclosed_collection (fun z => ordinalp z /\ ~limit_ordinal z)).
Proof.
move: OS_omega omega_limit => ha hb.
have pe: (forall x, inc x omega0 -> ordinalp x /\ ~ limit_ordinal x).
  move => x /(oltP ha) xo; have ox :=(proj31_1 xo).
  by split => //  /limit_ge_omega /(oltNge xo).
have pc: nonempty omega0 by exists \0o; apply: NS0. 
by move => [_ h]; case: (proj2 (h _ pe pc)); rewrite - [union _] omega_limit0.
Qed.


Lemma iclosed_normal_fun f x y: 
  ordinalp x -> ordinalp y -> normal_function f x y ->
  iclosed_set (Imf f).
Proof.
move => ox oy nf; move: (nf)=> [[ff sf tf] pb pc]; split.
  by move =>t /(Imf_Starget ff); rewrite tf => /(Os_ordinal oy).
move => F fr [w wf].
set G := Zo (source f) (fun z => inc (Vf f z) F).
have sgx: sub G x by rewrite - sf; apply:Zo_S.
have neG: nonempty G.
  move /(Imf_P ff): (fr _ wf) => [u uf uv]; exists u; apply:Zo_i => //; ue. 
have le1:=(ord_ub_sup1 ox sgx).
have sG: sub G (source f) by ue.
case: (equal_or_not (\osup G) x) => sx.
  have og:= Os_sub (Os_ordinal  ox) sgx.
  rewrite - sf in pb.
  left; apply: ord_sup_1cofinal; first split => //; last first.
    by move =>t  /(Imf_Starget ff); rewrite tf => /(Os_ordinal oy). 
  move => b /(Imf_P ff) [u usf ->].
  have ua': u <o \osup G by rewrite sx; apply /(oltP ox); ue.
  move: (olt_sup og ua') => [v vg uv].
  move /Zo_hi: (vg) => vf;ex_tac; exact: (proj1 (pb _ _ usf (Zo_S vg) uv)). 
have <-: Vfs f G = F.
  set_extens t; first by move /(Vf_image_P ff sG)=> [u /Zo_hi h ->].
  move => tF; apply  /(Vf_image_P ff sG).
  move /(Imf_P ff): (fr _ tF)=> [u usf uv]; exists u => //.
  apply: Zo_i => //; ue.
case: (normal_function_equiv ox oy nf sgx neG) => // <-; right.
apply /(Imf_P ff); exists (\osup G) => //; rewrite sf.
by apply/(oltP ox).
Qed.


Lemma iclosed_fixpoints_fun f a :
  ordinalp a -> normal_function f a a -> iclosed_set (fixpoints f).
Proof.
move => oa na; move:(na) => [[ff sf tf] pb pc].
rewrite /fixpoints sf; set E := Zo a _.
have ose: ordinal_set E by move =>t /Zo_S /(Os_ordinal oa).
split => // F fp nef.
have subfa: sub F a by move => t /fp /Zo_S.
have l1:= (ord_sup_M fp ose).
have h: \osup E <=o a by apply:ord_ub_sup1 => //; apply : Zo_S.
have l2:= (oleT l1 h).
case: (equal_or_not (\osup F) a) => sna.
  by rewrite - sna in h; left; apply:oleA.
case: (normal_function_equiv oa oa na subfa nef) => //.
have ->: (Vfs f F) = F.
  have aux: sub F (source f) by ue.
   set_extens t. 
     by move => /(Vf_image_P ff aux) [z zf ->]; rewrite (Zo_hi (fp _ zf)).
   by move => zf; apply /(Vf_image_P ff aux); ex_tac; rewrite (Zo_hi (fp _ zf)).
by move => fxp;right; apply: Zo_i => //; apply /(oltP oa).
Qed.

Lemma iclosed_fixpoints (f:fterm): normal_ofs f ->
    iclosed_proper (fun z => ordinalp z /\ f z = z).
Proof.
move => nf; split; last first.
  apply:unbounded_non_coll => x ox.
  move: (normal_ofs_fix nf ox) => [pa pb _]; have [_ oo _]:= pa.
  by exists (the_least_fixedpoint_ge f x). 
split; [by move => t [] | move => F fp nef ].
move /normal_ofs_equiv1: (nf) => [pa pb].
have pc: (forall x, inc x F -> \0o <=o x) by move =>x /fp [/ole0x ox _].
have pd: (fun_image F f) = F.
  set_extens t. 
     by move => /funI_P [z zf ->]; rewrite (proj2 (fp _ zf)).
  by move => tf; apply /funI_P; ex_tac; rewrite (proj2 (fp _ tf)).
move: (pb _ pc nef); rewrite pd => h; split => //; apply: OS_sup.
by move => t /pc [].
Qed.



Lemma iclosed_normal_ofs1 f u:
  ordinalp u -> normal_ofs1 f u ->  
  iclosed_proper (fun z => exists2 x, u <=o x & z = f x).
Proof.
move => ou [na nb].
have ha:= (ofs_sincru na).
have [_ [b ub h]] := (osum_increasing5 ou na).
split; last first.
  apply:unbounded_non_coll => x ox.
  case: (oleT_ee (proj32 ub) ox) => bx.
     exists (f x); [ by apply:h | exists x => //;apply: oleT ub bx].
  exists (f b); [exact: (oleT bx (h _ (oleR (proj32 ub)))) |by exists b].
split; first by move => x [y /ha uy ->].
move => F Fi nef.
pose p z t:= u <=o t /\ z = f t.
have pm z t: p z t -> t <=o (omax b z).
  move => [pa ->]; move:(ha _ pa) => oz.
  move: (omax_p1 (proj32 ub) oz) => [ma mb].
  case:(oleT_ee (proj32 ub) (proj32 pa)) => bt.
     exact:(oleT (h _ bt) mb).
  exact: (oleT bt ma).
pose g z := least_ordinal (p z) (omax b z).
have Cp a: u <=o a ->  u <=o (g (f a)) /\ (f a) = f (g (f a)).
  move =>  az; rewrite /g/least_ordinal; set E := Zo _ _ .
  have osE:ordinal_set E by move => t/Zo_P [_] [/proj32].
  have pp: p (f a) a by [].
  move: (pm  _ _ pp) => le1.
  have neE: nonempty E by exists a; apply:Zo_i =>//; apply/(oleP (proj32 le1)).
  by move:(least_ordinal0 osE neE) => [_ /Zo_P [ _ qb] _]. 
have CP1 a: u <=o a -> a = g (f a).
  move => au; move: (Cp _  au) => [pa pb].
  case: (oleT_ell (proj32 au) (proj32 pa)) => // hb.
    by move: (proj2 (na _ _ au hb)); rewrite {1} pb.
  by move: (proj2 (na _ _ pa hb)); rewrite - pb.
have CP2 x: inc x F -> p x (g x) by move /Fi => [t /Cp [ta tb] ->].
set E:= fun_image F g.
have Fv: F = fun_image E f.
  set_extens w.
   by move => wF; rewrite(proj2 (CP2 _ wF)); apply: funI_i; apply: funI_i.
  by move /funI_P => [x /funI_P [z  zf ->] ->]; rewrite - (proj2 (CP2 _ zf)).
have pa: forall x, inc x E -> u <=o x /\ g (f x) = x.
  by move => w /funI_P [z /CP2 [wa wb] ->];  rewrite - wb.
have Ea: (forall x, inc x E -> u <=o x) by move => x /pa [].
have [t0 t0f] := nef.
have fit0: inc (g t0) E by apply/funI_P; ex_tac.
have ne: nonempty E by ex_tac.
have: u <=o \osup E. 
  by apply: (oleT (Ea _ fit0)); apply: ord_sup_ub => // t /Ea [].
by move: (nb _ Ea ne); rewrite -Fv => ->; exists (union E). 
Qed.


Lemma iclosed_normal_ofs (f:fterm):  normal_ofs f  ->  
  iclosed_proper (fun z => exists2 x, ordinalp x & z = f x).
Proof.
move => h.
have sb: normal_ofs1 f \0o by apply/normal_ofs_equiv1.
move: (iclosed_normal_ofs1 OS0 sb)=> [[pa pb] pc].
have aux: forall z, (exists2 x, ordinalp x & z = f x) <->
                    exists2 x, \0o <=o x & z = f x.
  move => z; split; move => [x xp ->]; exists x => //; last by case: xp.
  exact:(ole0x xp).
split => //; first split.
+ by move => t [x ox ->]; apply(ofs_sincr (proj1 h)).
+ by move => g pF nef; apply /aux; apply: pb => // x/pF => w; apply/aux.
+ by move => [E ev]; case:pc; exists E => x; split; [move/ev/aux| move/aux/ev].
Qed.

Lemma normal_fix_points_similar f C (E:= cnext C)
      (Xi := Zo E (fun z => f z = z)):
  infinite_c C ->
  normal_ofs f ->
  (forall x, inc x E -> inc (f x) E) ->
  (ord_cofinal Xi E) /\ cardinal Xi = E.
Proof.
move => icE nf fee.
suff ha:  ord_cofinal Xi E by split => //;apply:ord_cofinal_p4.
split => //; first by apply: Zo_S.
move => x xE.
move: (next_fix_point_small icE nf fee xE).
move/(cnextP (proj1 icE)): (xE) => [ox ob].
move: (normal_ofs_fix nf ox) => []; set y := the_least_fixedpoint_ge f x.
by move => qa qb _ qc; exists y => //; apply:Zo_i.
Qed.


(** ** Indexing a collection of ordinals *)


Definition collectivising_srel (r: relation) :=
   forall x, r x x -> exists E, (forall y, inc y E <-> r y x).
Definition worder_rc r := worder_r r /\ collectivising_srel r.

Definition segmentr (r: relation) x :=
   choose (fun E => (forall y, inc y E <-> (r y x /\ y <> x))).

Definition ordinalr (r:relation) x := ordinal (graph_on r (segmentr r x)).

Lemma collectivising_srel_alt (r: relation): reflexive_rr r ->
  (collectivising_srel r <->  forall x,exists E, (forall y, inc y E <-> r y x)).
Proof.
move => rr; split => // H x; last by move => _; apply:H.
case: (p_or_not_p (r x x)) => hc; first by apply: H.
exists emptyset => y; split; [by move /in_set0 | by  move/rr => [] ].
Qed.

Lemma segmentrP r x: collectivising_srel r -> r x x ->
   (forall y, (inc y (segmentr r x) <-> r y x /\ y <> x)).
Proof.
move => pa pb; move: (pa _ pb) => [E Ep].
pose p E:= forall y, inc y E <-> r y x /\ y <> x.
rewrite -/(p _); apply: (choose_pr); exists (E -s1 x) => y; split.
  by move/setC1_P => [/Ep sa sb].
by move => [/Ep sa sb]; apply /setC1_P.
Qed.

Lemma worder_rc_seg (r: relation) x:
  worder_rc r -> r x x ->
  worder_on (graph_on r (segmentr r x)) (segmentr r x).
Proof.
move => [pa pb] rxx; apply: (wordering_pr pa).
move => a /(segmentrP pb rxx) [pc _].
by move: (pa) => [[_ _ rr] _]; move: (rr _ _ pc) => [].
Qed.

Lemma OS_ordinalr r x:
  worder_rc r -> r x x -> ordinalp (ordinalr r x).
Proof. by move => pa /(worder_rc_seg pa) [pc _]; apply: OS_ordinal. Qed.

Lemma ordinalr_Mle r x y: worder_rc r -> r x y ->
   (ordinalr r x) <=o (ordinalr r y).
Proof.
move => pa px.
move: (proj33 (proj1 (proj1 pa)) _ _ px) => [rxx ryy].
move: (proj1 (worder_rc_seg pa rxx))  (proj1 (worder_rc_seg pa ryy)) => ha hb.
apply: order_cp2 => //.
have ss: sub (segmentr r x) (segmentr r y).
  move => t /(segmentrP (proj2 pa) rxx)[sa sb].
  move: (proj31 (proj1 (proj1 pa)) _ _ _ sa px) => ty.
  apply/(segmentrP (proj2 pa) ryy); split => //.
  move => ety; rewrite - ety in px.
  by move: (proj32_1 (proj1 pa) _ _ sa px).
apply/(order_cp0 (proj1 ha) (proj1 hb)) => u v.
by move /graph_on_P1 => [sa sb sc]; apply /graph_on_P1; split => //; apply: ss.
Qed.

Lemma ordinalr_Mlt (r:relation) x y: worder_rc r -> r x y -> x <> y ->
   (ordinalr r x) <o (ordinalr r y).
Proof.
move => pa px xny.
move: (pa) => [[[rt ra rr] _] csr].
have [rxx ryy] := (rr _ _ px).
move: (segmentrP csr rxx) (segmentrP csr ryy) => sx sy.
have ss: sub (segmentr r x) (segmentr r y).
  move => t /sx [sa sb].
  move: (rt _ _ _ sa px) => ty; apply/sy; split => //.
  dneg ety; rewrite - ety in px.
  exact: (ra _ _ sa px).
move: (proj1 (worder_rc_seg pa rxx)) (proj1 (worder_rc_seg pa ryy)) => ha hb.
have pb: sub (graph_on r (segmentr r x)) (graph_on r (segmentr r y)).
  apply/(order_cp0 (proj1 ha) (proj1 hb)) => u v.
  by move/graph_on_P1 => [sa sb sc]; apply /graph_on_P1; split => //; apply: ss.
have pc: forall z, r z z ->  
   substrate (graph_on r (segmentr r z)) = (segmentr r z). 
  move => z rzz; apply :graph_on_sr => a /(segmentrP csr rzz) [xx _].
  by move: (rr _ _ xx) => [].
have xsy: inc x (segmentr r y) by apply /sy.
apply: order_cp3 => //.
  split => // /(f_equal substrate).
  rewrite (pc _ rxx) (pc _ ryy) => h.
  by move: xsy; rewrite -h; move/sx =>[_].
rewrite (pc _ rxx); hnf; rewrite (pc _ ryy); split => //.
move => a b /sx [sa sb] /graph_on_P1 [h1 h2 h3]; apply /sx.
move: (rt _ _ _ h3 sa) => bx; split => // ebx.
by rewrite ebx in h3; move: (ra _ _ sa h3).
Qed.

Lemma ordinalr_segment (r:relation) a x (b:=ordinalr r x): 
   worder_rc r -> r x x -> a <=o b ->
   (exists2 y, r y y & a = ordinalr r y).
Proof.
move => woc rxx ab.
case:(ole_eqVlt ab); [by move ->; exists x | move => /(oltP (proj32 ab)) iab].
have [pa pb] := (worder_rc_seg woc rxx).
move: (the_ordinal_iso1 pa) => [].
rewrite -/(ordinalr _ _) pb ordinal_o_sr.
set gr := (graph_on r (segmentr r x)); set f := (the_ordinal_iso gr).
set oor := (ordinal_o (ordinalr r x)). 
move => sa sb [[[ff injf] [_ sjf]] sf tf] sd.
have asf: inc a (source f) by ue.
move: (Vf_target ff asf); rewrite tf.
set y := Vf f a; set rs:= (graph_on r (segmentr r y)).
move /(segmentrP (proj2 woc) rxx) => [ryx xny].
have or:= (proj1 (proj1 woc)).
move: (proj33 or _ _ ryx) => [ryy _].
have sP:=(segmentrP (proj2 woc) ryy).
set g:= Lf (Vf f) a (segmentr r y). 
have [oa ob sab] := ab.
suff oih:order_isomorphism g (ordinal_o a) rs.
  have h : ordinal_o a \Is rs by exists g.
  have tt:= (worder_invariance h (ordinal_o_wor oa)).
  by exists y => //; rewrite - (ordinal_o_isu2 tt oa (orderIS h)).
have srr: substrate rs = (segmentr r y). 
   by apply:graph_on_sr => u /sP [/(proj33 or) []].
have saf: sub a (source f) by ue.
have la: lf_axiom (Vf f) a (segmentr r y).
  move => s ssa; have isf :=(saf _ ssa). 
  move/(oltP oa): ssa => [la na].
  apply /sP; split; last  by move/(injf  _ _ isf asf).
  have:gle oor s a. 
    by apply /graph_on_P1;rewrite - sf; split => //; case:la.
  by move /(sd s a isf asf) => /graph_on_P1 [].
hnf; rewrite (ordinal_o_sr) srr.
split => //; [ fprops | apply: (order_from_rel _ or) |  |].
  hnf; rewrite /g; saw; apply: lf_bijective => //.
    by move => u v ua va; apply injf; apply: saf.
  move => c /sP [c1 c2].
  have: inc c (target f).
     rewrite tf; apply /(segmentrP (proj2 woc) rxx).
     move: (proj31 or _ _ _ c1 ryx)=> cx; split => //.
     by move => ecx; rewrite -ecx in ryx;move: (proj32  or _ _ c1 ryx).
  move /sjf => [d dsf dv]; exists d; last by rewrite dv.
  have od: ordinalp d by rewrite sf in dsf; exact: (Os_ordinal ob dsf).
  case:(oleT_si oa od) => // sad.
  have: gle oor a d by apply /sub_gleP; split => //; ue.
  move /(sd _ _ asf dsf) => /graph_on_P1 [_ _];rewrite -dv -/y => yc.
  case: c2; exact (proj32 or  _ _ c1 yc).
hnf; rewrite /g;aw => u v ua va; rewrite !LfV//.
move: (saf _ ua) (saf _ va) =>ub vb.
have h:= (sd u v ub vb).
split. 
  move/sub_gleP=> [_ _ h1]; apply/graph_on_P1; split; try apply: la => //.
  suff:gle gr (Vf f u) (Vf f v) by move/graph_on_P1 =>[].
  by apply /h; apply/sub_gleP; rewrite - sf. 
move/graph_on_P1 => [_ _ h1]; apply/sub_gleP; split => //.
suff:gle gr (Vf f u) (Vf f v) by  move/h /sub_gleP=> [].
apply/graph_on_P1; split => //; Wtac. 
Qed.

Definition ordinals (r:relation) a := 
  choose (fun x => r x x /\ a = ordinalr r x).

Lemma ordinalsP (r:relation) a:  worder_rc r ->
  (exists2 x, r x x & a = ordinalr r x) ->
  (r (ordinals r a) (ordinals r a) /\ ordinalr r (ordinals r a) = a).
Proof.
move => pa [x rxx av].
pose p x := (r x x /\ a = ordinalr r x).
rewrite /ordinals -/p.
have exp : exists x, p x by exists x.
by move: (choose_pr exp); set q := (choose p); move => [rqq ->].
Qed.

Lemma ordinalsrP (r:relation) x:  worder_rc r -> r x x ->
  ordinals r (ordinalr r x) = x.
Proof.
move => pa pb.
set a := (ordinalr r x).
have: (exists2 x, r x x & a = ordinalr r x) by exists x.
move /(ordinalsP pa); set q := ordinals r a;  move => [rqq qv].
ex_middle bad.
case: (worderr_total (proj1 pa) rqq pb) => h.
  by move: (ordinalr_Mlt pa h bad) => [_]; rewrite qv.
by move: (ordinalr_Mlt pa h (nesym bad))=> [_]; rewrite qv.
Qed.

Lemma ordinals_non_coll1 r:  worder_rc r ->
   (non_coll (fun x => r x x)) ->
   (forall a, ordinalp a -> exists2 x, r x x & a = ordinalr r x).
Proof.
move => pa pb a oa; ex_middle npa; case: pb.
exists (Zo (fun_image a (ordinals r)) (fun z => r z z)).
move => x; split; first by move /Zo_hi.
move => rxx; apply /Zo_P; split => //; apply /funI_P.
rewrite - (ordinalsrP pa rxx).
case: (oleT_el oa (OS_ordinalr pa rxx));first by move/(ordinalr_segment pa rxx).
by move /oltP0 => [_ _ za]; ex_tac. 
Qed.

Lemma ordinals_Mle r a b:  worder_rc r ->
   (non_coll (fun x => r x x)) ->
   a <=o b -> r (ordinals r a) (ordinals r b).
Proof.
move => ha hb ab.
move: (ordinalsP ha (ordinals_non_coll1 ha hb (proj31 ab))).
move: (ordinalsP ha (ordinals_non_coll1 ha hb (proj32 ab))).
set sa := (ordinals r a); set sb := (ordinals r b).
move => [rbb vb][raa va].
case: (worderr_total (proj1 ha) raa rbb) => // h.
move:(ordinalr_Mle ha h); rewrite va vb => ba.
by move: raa; rewrite /sa /sb (oleA ab ba).
Qed.

Lemma ordinals_Mlt r a b:  worder_rc r ->
   (non_coll (fun x => r x x)) ->
   a <o b -> 
  (r (ordinals r a) (ordinals r b) /\  (ordinals r a) <>  (ordinals r b)).
Proof.
move => pa pb [pc pd]; move:(ordinals_Mle pa pb pc) => h.
split => // sv.
move: (pc) => [oa ob _].
case: pd.
rewrite - (proj2 (ordinalsP pa (ordinals_non_coll1 pa pb oa))).
by rewrite - (proj2 (ordinalsP pa (ordinals_non_coll1 pa pb ob))) sv.
Qed.

Lemma collectivising_srel_ord (r:relation):
  (forall x y, r x y -> x <=o y) -> collectivising_srel r.
Proof.
move => h1 x /h1 xx.
have ox:= (proj31 xx).
exists (Zo (osucc x) (r^~ x)); move => y;split; first by move /Zo_hi.
by move => ryx; apply:Zo_i => //; apply /(oleP ox); apply: h1.
Qed.

Lemma collectivising_srel_ord_seg (r:relation) : 
  (forall x y, r x y -> x <=o y) -> 
  forall x, r x x -> segmentr r x = Zo x (fun z => r z x).
Proof.
move => ro x rxx.
have ox:=(proj31 (ro _ _ rxx)).
have cr:=(collectivising_srel_ord ro).
set_extens t.
  move /(segmentrP cr rxx) => [pa pb]; apply: Zo_i; last exact:pa.
  by apply/(oltP ox); split => //; apply: ro.
move => /Zo_P[pa pb]; apply /(segmentrP cr rxx); split => //.
by move=> tx; case: (ordinal_decent ox pa); rewrite {2} tx.
Qed.

Lemma worder_rc_ord (r:relation) : 
  (forall x y, r x y -> x <=o y) ->
  (order_r r) -> (forall x y, r x x -> r y y -> (r x y \/ r y x)) ->
  worder_rc r.
Proof.
move=> h1 h2 h3; split.
  split => // x hx [w wx].
  have ow:= (proj31 (h1 _ _ (hx _ wx))).
  move: (least_ordinal4 ow wx (p:=inc^~x)); set y := least_ordinal _ _.
  move=> [oy yx yl]; rewrite /has_least/least (graph_on_sr hx). 
  exists y; split => //.
  move => t tx; apply /graph_on_P1; split => //.
  case: (h3 _ _ (hx _ yx) (hx _ tx)) => // /h1 ty.
  have ot:= (proj31 (h1 _ _ (hx _ tx))).
  by move: (yl _ ot tx) => yt; rewrite (oleA ty yt); apply: hx.
move => x /h1 xx.
have ox:= (proj31 xx).
exists (Zo (osucc x) (r^~ x)); move => y;split; first by move /Zo_hi.
by move => ryx; apply:Zo_i => //; apply /(oleP ox); apply: h1.
Qed.

Lemma worder_rc_op (p:property) :
  worder_rc (fun x y => [/\ p x, p y & x <=o y]).
Proof.
apply: worder_rc_ord.
- by move => x y [_ _].
- split.
  + move =>x y z [pa pb pc][pd pe pf]; split => //; exact: oleT pc pf.
  + move =>x y  [_ _ pc][ _ _  pf]; exact: oleA pc pf.
  + by move => x y [pa pb [pc pd _]]; split; split => //; apply: oleR.
- move => x y [pa _ [pc _ _]][ pb _  [pf _ _]].
  by case: (oleT_ee pc pf) => le; [left | right]; split.
Qed.

Lemma ordinalrsP (p: property) (r := fun x y => [/\ p x, p y & x <=o y])
   x (y := ordinalr r x): 
   ordinal_prop p -> p x -> (ordinalp y) /\ ordinals r y = x. 
Proof.
move => op px; move:(op _ px) => ox.
move: (worder_rc_op p) => pa.
have rxx: r x x by split => //; apply:oleR.
move:(ordinalsrP pa rxx) => h; split => //; by apply: OS_ordinalr.
Qed.

Lemma ordinals_set_iso E (p := inc ^~E)
      (r:= fun x y => [/\ p x, p y & x <=o y])
      (A:= ordinal (ole_on E)): 
  (ordinal_set E) -> 
  (lf_axiom  (ordinals r) A E) /\
  order_isomorphism (Lf (ordinals r) A E) (ordinal_o A) (ole_on E).
Proof.
move => pa.
move: (worder_rc_op p) ; rewrite -/r => pc.
have ose: (forall a, inc a E -> a <=o a) by move => a /pa op; apply:oleR.
have rxx: forall x, r x x <-> inc x E.
  move => x; split; [ by move =>[] | move => xE;split; fprops ].
pose H a := (exists2 x, r x x & a = ordinalr r x).
have pd: forall a, H a ->
    (r (ordinals r a) (ordinals r a) /\ ordinalr r (ordinals r a) = a).
  by move => a ha; apply:  ordinalsP.
have pe: forall x, inc x E -> ordinals r (ordinalr r x) = x.
  by move => x /rxx xe;apply:  ordinalsrP.
move: (wordering_ole_pr pa) => [sc sd].
have ra: forall x, inc x E -> inc (ordinalr r x) A.
  move => x /rxx xE; suff: (ordinalr r x) <o A by move /oltP0 => [].
  move: (worder_rc_seg pc xE) => []; rewrite -/r => [sa sb].
  move: (segmentrP (proj2 pc) xE); rewrite -/r => sp.
  apply: order_cp3 => //; first split.
  + apply /(order_cp0 (proj1 sa) (proj1 sc))=> u v.
    by move/graph_on_P1 => [_ _ uv];apply/graph_on_P1. 
  + move => /(f_equal substrate); rewrite sb sd => ss.
    by move /rxx:(xE); rewrite - ss; move /sp => [_].
  + hnf; rewrite sb sd;split; first by move =>t /sp [] [].
    move => u v /sp [[pu px ux] nux] /graph_on_P1 [ve _ vu]; apply /sp; split.
      split => //; apply:oleT vu ux.
    move => vx; case: nux; rewrite vx in vu; apply:oleA ux vu.
have rb:forall a, inc a A -> H a.
  move => a aA.
  move: (the_ordinal_iso1 sc); rewrite -/A; set f:= the_ordinal_iso _. 
  rewrite /order_isomorphism sd ordinal_o_sr. 
  move => [sa sb [[[ff injf] [_ sjf]] sf tf] isf].
  hnf in isf; rewrite sf in injf isf.
  set x := Vf f a.
  have xe: r x x by apply /rxx;rewrite - tf /x; Wtac. 
  have [ta tb] :=(worder_rc_seg pc xe).
  have oA:ordinalp A by exact: (OS_ordinal sc). 
  have oa :=(Os_ordinal oA aA).
  have saA :=(ordinal_transitive oA aA).
  exists x => //; symmetry;rewrite /ordinalr;apply: ordinal_o_isu2 => //.
  have la: lf_axiom (Vf f) a (segmentr r x).
    move => t ita; move: (saA _ ita) => tA.
    have [[_ _ lte] nta]: t <o a by apply /oltP.
    have: gle (ordinal_o A) t a by apply /sub_gleP.
    move /(isf _ _ tA aA) => /graph_on_P1.
    move => h; apply /(segmentrP (proj2 pc) xe); split => //.
    by move => hh; case: nta; apply/ (injf _ _ tA aA).
  apply:orderIS;exists (Lf (Vf f) a (segmentr r x)).
  hnf; rewrite tb ordinal_o_sr; split; fprops.
    hnf; saw; apply: lf_bijective => //.
      move => u v /saA ua /saA va; apply /(injf _ _ ua va).
    move => y /(segmentrP (proj2 pc) xe) [[yE _ rxy] xny].
    rewrite tf in sjf;move: (sjf _ yE) => [];rewrite sf => [b bA bb].
    case: (oleT_el (Os_ordinal oA aA) (Os_ordinal oA bA)).
      move => [_ _ ab]; have: gle (ordinal_o A) a b by apply /sub_gleP.
      move /(isf _ _ aA bA) => /graph_on_P1 [_ _];rewrite -bb - /x => xy.
      case: xny; apply:oleA rxy xy.
    move /(oltP oa) => ba; ex_tac.
  hnf;aw;move => u v ua va; rewrite !LfV//. 
  move: (saA _ ua) (saA _ va) => uA vA; split.
    move/sub_gleP=> [_ _ h1]; have: gle (ordinal_o A) u v by apply /sub_gleP.
    move /(isf _ _ uA vA) => /graph_on_P1 [_ _ le].
    apply/graph_on_P1; split;try apply: la => //; split => //; rewrite /p; Wtac.
  move /graph_on_P1 => [_ _ [_ _ le]].
  have:(gle (ole_on E) (Vf f u) (Vf f v)).
    apply/graph_on_P1; split => //; Wtac.
  by move /(isf _ _ uA vA) => /sub_gleP [_ _ h1]; apply/sub_gleP.
set fp := ordinals r.
have rc: forall a, inc a A -> inc (fp a) E /\ ordinalr r (fp a) = a.
  by move => a /rb /pd [/rxx sa sb].
set f := Lf fp A E.
have lfa: lf_axiom fp A E by move => t /rc [].
have bf: bijection_prop f A E.
  hnf;rewrite /f; saw; apply: lf_bijective.
  - by exact.
  - by move => u v /rc [_  e1] /rc [_ e2] e3; rewrite - e1 - e2 e3.
  - by move => y yE; rewrite -(pe _ yE); move: (ra _ yE) => h; ex_tac. 
split => //.
split => //; [ apply: ordinal_o_or | fprops | by rewrite ordinal_o_sr sd |].
hnf; rewrite /f; aw; move => x y xA yA; rewrite !LfV//.
move: (rc _ xA) (rc _ yA) => [ta tb][tc td]; split => h.
  move:(proj2 (worder_total sc));rewrite sd => to;case: (to _ _ ta tc) => //hh.
  move /sub_gleP:h => [_ _ ce].
  suff: x = y by move => h1; move: hh; rewrite h1.
  move/graph_on_P1:hh => /(ordinalr_Mle pc).
  by rewrite tb td; move => [_ _ cp]; apply: extensionality. 
move/graph_on_P1:h => /(ordinalr_Mle pc). 
by rewrite tb td; move => [_ _ cp];apply/sub_gleP.
Qed.

Lemma ordinals_set_normal E (p := inc ^~E)
      (r:= fun x y => [/\ p x, p y & x <=o y])
      (A:= ordinal (ole_on E))
      (f:= Lf (ordinals r) A E): 
  (iclosed_set E) -> 
  normal_function f A E.
Proof.
move => [pa pb].
move: (proj2 (ordinals_set_iso pa)); rewrite -/f -/A.
move => [o1 o2 [[[ff injf] [_ sjf]] sf tf] fincr].
move: (worder_rc_op p) ; rewrite -/r => pc.
move: (wordering_ole_pr pa) => [sc sd].
rewrite sd in tf; rewrite ordinal_o_sr in sf.
have fi: forall a b, inc a A -> inc b A -> a <o b -> Vf f a <o Vf f b.
   hnf in fincr; rewrite sf in fincr injf.
   move => a b asf bsf [lab nab]; split.
     have: gle (ordinal_o A) a b by move: lab => [_ _ lab]; apply/sub_gleP.
     by move /(fincr _ _ asf bsf) => /graph_on_P1 [].
   by move => h; move: (injf _ _ asf bsf h).
split => // a aA la.
have oA:=(OS_ordinal sc). 
set F :=(Vfs f a). 
have asf: sub a (source f) by rewrite sf; apply: (ordinal_transitive oA).
have sfe: sub F E by rewrite -tf ; apply:fun_image_Starget1.
have nef: nonempty F. 
   exists (Vf f \0o); apply /(Vf_image_P ff asf); exists \0o => //.
   exact: (proj32 la).
have osF:= Os_sub pa sfe.
have faE: inc (Vf f a) E by rewrite -tf; Wtac.
have suE:= (ord_sup_ub pa faE).
have ofa:= (pa _ faE).
have bfa : ordinal_ub F (Vf f a).
  move => t /(Vf_image_P ff asf) [u ua ->].
  have uA:= (ordinal_transitive oA aA ua).
  move /(oltP (proj31 la)): ua => ua.
  exact: (proj1 (fi _ _ uA aA ua)).
have pr1:=(ord_ub_sup ofa bfa).
case: (pb _ sfe nef) => H; first by rewrite - H in suE; apply: (oleA suE pr1).
rewrite tf in sjf; move: (sjf _ H); rewrite sf; move => [b bA bv].
move: (Os_ordinal oA aA) (Os_ordinal oA bA) => oa ob.
case: (oleT_ell oa ob) => ab; first by ue.
  by move: (fi _ _ aA bA ab); rewrite - bv => /(oleNgt pr1).
have sb: osucc b <o a by move /(limit_ordinal_P): la => [ _]; apply.
have sbb: inc  (osucc b) a by apply /(oltP oa).
have osbA:=(ordinal_transitive oA aA sbb). 
have h:= (fi _ _ bA osbA (oltS ob)).
have: inc (Vf f (osucc b)) F by  apply/(Vf_image_P ff asf); ex_tac.
by move /(ord_sup_ub osF); rewrite bv => /(oltNge h).
Qed.

Definition ordinalsE E B :=  
  Lf (ordinals (fun x y => [/\ inc x B, inc y B & x <=o y])) E E.

Lemma ordinals_set_normal1 C (E:= cnext C) B (f:= ordinalsE E B):
  infinite_c C -> iclosed_set B -> ord_cofinal B E ->
  [/\ lf_axiom (ordinals (fun x y=> [/\ inc x B, inc y B & x <=o y])) E E ,
    normal_function f E E & Imf f = B].
Proof.
move => pa pb pc.
move: (ord_cofinal_p5 pa pc); rewrite -/E => eq1.
move: (ordinals_set_normal pb) (ordinals_set_iso (proj1 pb)).
rewrite eq1; set g := (Lf (ordinals _) E B); move => [p1 p2 p3] [pd pe].
have sbe: sub B E by move: pc => [].
have pf: lf_axiom (ordinals (fun x y=> [/\ inc x B, inc y B & x <=o y])) E E 
   by move => t /pd /sbe.
have ff: function f by apply: lf_function.
have fg: function g by apply: lf_function.
have oe: ordinalp E by move:(cnext_pr1 (proj1 pa)) => [[]]. 
have sf: forall x, inc x E -> Vf f x = Vf g x.
  by move => x xe; rewrite /f/ordinalsE/g !LfV.
have imf: Imf f = B.
   set_extens t. 
     move /(Imf_P ff); rewrite /f /ordinalsE; aw.
     by move=> [u ua ->]; rewrite LfV//; apply: pd.
   move => tb;move: pe => [_ _ [[_ [_ p4]] _ _] _].
   have ttg: inc t (target g) by rewrite /g; aw.
   have sg: source g  = E by rewrite /g; aw.
   move: (p4 _ ttg) => [u ua ->]; rewrite - sf; last by ue.
   apply /(Imf_P ff); exists u => //;rewrite /f/ordinalsE; aw; ue.
split => //; split => //.
+ by rewrite /f /ordinalsE/function_prop;aw.
+ by move => x y xe ye xy; rewrite sf // sf //; apply: p2.
+ move => x xe lx; rewrite sf // (p3 x xe lx). 
  have sxe :=(ordinal_transitive oe xe).
  have sa: sub x (source g) by rewrite /g; aw.
  have sb: sub x (source f) by rewrite /f/ordinalsE; aw.
  congr union; set_extens y.
    move /(Vf_image_P fg sa) => [u ux ->]; rewrite - sf //; last by apply: sxe.
    apply /(Vf_image_P ff sb); ex_tac.
  move /(Vf_image_P ff sb) => [u ux ->]; rewrite  sf //; last by apply: sxe.
  apply /(Vf_image_P fg sa); ex_tac.
Qed.

Lemma ordinals2_extc C1 C2 B1 B2
    (E1 := cnext C1)(E2 := cnext C2) :
  infinite_c C1 -> infinite_c C2 ->
  iclosed_set B1 -> iclosed_set B2 -> 
  ord_cofinal B1 E1 -> ord_cofinal B2 E2 ->
  C1 <=c C2 -> B1 = B2 \cap E1 ->
  agrees_on E1 (ordinalsE E1 B1) (ordinalsE E2 B2).
Proof.
move => ic1 ic2 cl1 cl2 cf1 cf2 c1c2 iv.
move: (ordinals_set_normal1 ic1 cl1 cf1).
move: (ordinals_set_normal1 ic2 cl2 cf2).
rewrite -/E1 -/E2.
set f1 := (ordinalsE E1 B1); set f2 := (ordinalsE E2 B2).
move => [ax2 [[ff2 sf2 tf2] ninc2 cont2] im2].
move => [ax1 [[ff1 sf1 tf1] ninc1 cont1] im1].
have E1E2: sub E1 E2 by exact:(proj33 (cnext_pr6  c1c2)).
have B1B2: sub B1 B2 by rewrite iv; apply: subsetI2l.
have oe2: ordinalp E2 by move:(cnext_pr1 (proj1 ic2)) => [[]]. 
have oe1: ordinalp E1 by move:(cnext_pr1 (proj1 ic1)) => [[]]. 
have ob2: ordinal_set B2 by move => t /(proj1 cf2) /(Os_ordinal oe2).
have ob1: ordinal_set B1 by move => t /B1B2 /ob2.
move: (ordinals_set_iso ob1) => [].
rewrite (ord_cofinal_p5  ic1 cf1).
move: (ordinals_set_iso ob2) => [].
rewrite (ord_cofinal_p5  ic2 cf2).
set r1 :=  (fun x y => [/\ inc x B1, inc y B1 & x <=o y]).
set r2 :=  (fun x y => [/\ inc x B2, inc y B2 & x <=o y]).
rewrite -/E1 -/E2; move => ua2 ub2 ua1 ub1.
move: (inverse_order_is ub2).
set g2 := (Lf (ordinals r2) E2 B2); set g2' := inverse_fun g2 => ub3.
have sr2: (substrate (ole_on B2)) = B2.
  by rewrite graph_on_sr // => a /ob2 /oleR.
have sr1: (substrate (ole_on B1)) = B1.
  by rewrite graph_on_sr // => a /ob1 /oleR.
move: (proj43 ub3); rewrite sr2 ordinal_o_sr => bg2.
have sg2: source g2' = B2 by  move: bg2 => [_ fb _].
have sa: forall x, inc x E1 -> inc (Vf g2' (ordinals r1 x)) E2.
  move => x /ua1 /B1B2 xsf; move: bg2 => [[[fa _] _] _ fc]; Wtac.
set g3 := Lf (fun x => (Vf g2' (ordinals r1 x)))  E1 E2.
have isoc: order_morphism g3 (ordinal_o E1) (ordinal_o E2).
  move: ub1 ub3 => [pa _ _ pb] [_ pc _ pd].
  split => //. 
    by rewrite !ordinal_o_sr /g3; hnf; saw; apply:lf_function.
  hnf;rewrite /g3; aw => x y xe1 ye1; rewrite !LfV//.
  move: (pb x y);aw; rewrite !LfV// => h; move: (h xe1 ye1).
  set x' := (ordinals r1 x); set y' := (ordinals r1 y) => hh.
  have x'b2: inc x' B2 by  apply/B1B2 /ua1.
  have y'b2: inc y' B2 by  apply/B1B2 /ua1.
  move:(pd x' y'); rewrite sg2 => h'; move: (h' x'b2 y'b2) => hh'.
  apply: (iff_trans hh). split => //.
    by move => /graph_on_P1  [_ _ ok]; apply /hh' /graph_on_P1.
  move/hh' /graph_on_P1 => [_ _ ok]; apply /graph_on_P1.
  by split => //; apply:ua1.
set g4 := Lf id E1 E2. 
have isod : order_morphism g4 (ordinal_o E1) (ordinal_o E2).
  move: isoc => [pa pb _ _]; split => //.
    rewrite !ordinal_o_sr /g4; hnf; saw; apply: lf_function => //.
  hnf;rewrite /g4; aw => x y xe1 ye1; rewrite !LfV//;  split => //.
      move => /graph_on_P1  [_ _ ok]; apply  /graph_on_P1. 
     by split => //; apply:E1E2.
  by move /graph_on_P1 => [_ _ ok]; apply /graph_on_P1.
have wo2: worder (ordinal_o E2) by apply: ordinal_o_wor. 
have wo1: worder (ordinal_o E1) by apply: ordinal_o_wor.
have s1: segmentp (ordinal_o E2) (Imf g3).
   move: isoc=> [ _ _ [fg3 sg3 tg3] _].
   split.
     by move => t /(Imf_P fg3); rewrite  - tg3; move => [ x xe1 ->]; Wtac.
   move => x y /(Imf_P fg3) [x1 x1s ->] l2.
   have xe1: inc x1 E1 by  move:x1s; rewrite sg3 ordinal_o_sr.
   move /ordo_leP: (l2)  => [ye2 gx ll]; apply /(Imf_P fg3).
   move: ub2 => [_ _ [bg sg tg2] h2]; move: (h2 y (Vf g3 x1)); aw.
   rewrite LfV// => h3.
   move /(h3 ye2 gx): l2.
   have inc1: inc (ordinals r1 x1) B1 by apply :ua1.
   have eq2: (ordinals r2 (Vf g3 x1)) = ordinals r1 x1.
     transitivity (Vf g2  (Vf g3 x1)); first by rewrite /g2 LfV.
     by rewrite /g3 LfV //;apply: inverse_V => //; rewrite tg2 sr2; apply /B1B2.
   rewrite LfV // eq2; move /graph_on_P1=> [sa1 sb1 sc1].
   move: ub1=> [_ _ [bg1 sg1 tg1] _].
   have y'b1: inc (ordinals r2 y)  (target (Lf (ordinals r1) E1 B1)).
       rewrite tg1 sr1 iv; apply /setI2_P; split => //.
       move: (proj1 cf1 _ inc1) => /(oltP oe1) lt2.
       apply /(oltP oe1); exact:ole_ltT sc1 lt2.
   have eq3: (ordinals r2 y) = Vf g2 y by rewrite /g2 LfV.
   move: (proj2 (proj2 bg1) _ y'b1) => [z];  rewrite lf_source => ze1.
   rewrite LfV// => zv; rewrite /g3; aw; exists z => //; rewrite LfV//.
   by rewrite - zv eq3 inverse_V2 // sg ordinal_o_sr.
have s2:segmentp (ordinal_o E2) (Imf g4).
  hnf;rewrite/g4  - canonical_injectionE (ci_range E1E2) ordinal_o_sr.
  split => // x y /(oltP oe1) xe1 /graph_on_P1 [/(oltP oe2) ye2 _ xy].
  apply/(oltP oe1); exact:(ole_ltT (And3 (proj31_1 ye2) (proj31_1 xe1) xy) xe1).
move: (isomorphism_worder_unique  wo1 wo2 s1 s2 isoc isod) => g3g4.
hnf; rewrite sf1 sf2; split => // x xe1.
have xe2 := (E1E2 _ xe1).
rewrite /f1 /f2 /ordinalsE; aw; rewrite -/r1 -/r2.
move: ub2 => [_ _ [bg _ tg] _].
have tg2: target g2 = B2 by  move: tg; rewrite -/g2 sr2.
move: (f_equal (Vf^~ x) g3g4); rewrite /g3 /g4 !LfV // => eq1.
move: (f_equal (Vf g2) eq1); rewrite {2} /g2 LfV//.
by rewrite inverse_V //; rewrite tg2; apply /B1B2/ ua1.
Qed.


Definition ordinalsf (p: property) :=
   ordinals (fun x y  => [/\ p x,  p y  & x <=o y]).

Lemma ordinals_col_p1 (p: property) (f := ordinalsf p):
   (forall x, p x -> ordinalp x) -> (non_coll p) ->
 [/\ 
    forall a, ordinalp a -> p (f a),
    forall x, p x -> exists2 a, ordinalp a & x = f a,
    forall a b, a<=o b -> (f a) <=o (f b),
    forall a b, a<o b -> (f a) <o (f b) &
    (forall a b, ordinalp a -> ordinalp b -> (a<=o b <-> (f a) <=o (f b))) /\
    forall a b, ordinalp a -> ordinalp b -> (a<o b <-> (f a) <o (f b))].
Proof.
move => pa pb.
set r :=  (fun x y => [/\ p x,  p y  & x <=o y]).
have pc: (non_coll (fun x => r x x)).
  move => [E Ep]; case: pb; exists E => x; split; first by move /Ep => [].
  by move => px; apply /Ep; split => //; move: (pa _ px) => /oleR.
move: (worder_rc_op p) => pd.
have le0: forall a, ordinalp a -> p (f a).
  by move => a oa; move: (ordinals_Mle pd pc (oleR oa)) => [].
have lt1: forall a b, a <o b -> (f a) <o (f b).
  by move => a b h; move: (ordinals_Mlt pd pc h) => [[_ _]]. 
have le1: forall a b, a<=o b -> (f a) <=o (f b).
  by move => a b h; move: (ordinals_Mle pd pc h) => [_ _]. 
have lt2:forall x, p x -> exists2 a, ordinalp a & x = f a.
  move => x px.
  have h: r x x by split => //; move: (pa _ px) => /oleR ox.
  move:(ordinalsrP pd h) (OS_ordinalr pd h); rewrite -/r -/f => h1 h2.
  by exists (ordinalr r x).
split => //; split.
  move => a b oa ob; split => h; first by apply: le1.
  by case: (oleT_el oa ob) => // /lt1 /(oleNgt  h).
move => a b oa ob; split => h; first by apply: lt1.
by case: (oleT_el ob oa) => // /le1 /(oltNge h).
Qed.

Lemma ordinals_col_p2 (p: property) (f := ordinalsf p):
   (iclosed_proper p) -> 
   normal_ofs f.
Proof.
move => [[pa pb] pc].
set r :=  (fun x y => [/\ p x,  p y  & x <=o y]).
move: (ordinals_col_p1 pa pc); rewrite -/r -/f; move => [s1 s2 s3 s4 [s5 s6]].
split=> // a la.
have [oa zea lla] := la.
set F :=(fun_image a f).
have nef: nonempty F by apply: funI_setne; ex_tac.
have Fp: (forall x, inc x F -> p x). 
  move => t /funI_P[z za ->]; apply:s1 (Os_ordinal oa za).
have osF: ordinal_set F  by move => t /Fp/pa. 
move: (pb _ Fp nef) => puF.
have bfa : ordinal_ub F (f a).
  by move => t /funI_P [z /(oltP oa) [za _] ->]; apply:s3.
have ofa:= (pa _ (s1 _ oa)).
move: (ord_ub_sup ofa bfa). 
move: (s2 _ puF) => [b ob bv]; rewrite bv => p1.
case: (oleT_el oa ob) => cab; first exact :(oleA (s3 _ _ cab) p1).
move:(s4 _ _  (oltS ob)) => h.
have sb: osucc b <o a by move /(limit_ordinal_P): la => [ _]; apply.
have sbb: inc (osucc b) a by apply /(oltP oa).
have: inc (f (osucc b)) F by apply/funI_P; ex_tac.
by move /(ord_sup_ub osF); rewrite bv=> /(oltNge h).
Qed.


Lemma iclosed_col_f0  (p: property) (f := ordinalsf p) (x:= f \0o):
  (iclosed_proper p) -> 
  (p x /\ (forall z, p z -> x <=o z)).
Proof.
move => [[pa pb] pc].
set r :=  (fun x y => [/\ p x,  p y  & x <=o y]).
move: (ordinals_col_p1 pa pc); rewrite -/r -/f; move => [s1 s2 s3 s4 [s5 s6]].
split; first by apply: s1; fprops.
by move => z /s2 [a /ole0x oa ->]; apply: s3.
Qed.

Lemma iclosed_col_fs  (p: property) (f := ordinalsf p) a 
   (x:= f a) (y := f (osucc a)) :
  (iclosed_proper p) -> ordinalp a ->
  [/\ x <o y, p x, p y &  (forall z, p z -> x <o z -> y <=o z)].
Proof.
move => [[pa pb] pc] oa.
set r :=  (fun x y => [/\ p x,  p y  & x <=o y]).
move: (ordinals_col_p1 pa pc); rewrite -/r -/f; move => [s1 s2 s3 s4 [s5 s6]].
have ob:=(OS_succ oa).
move: (s4 _ _  (oltS oa)) => h; split => //; try apply: s1 => //. 
move => z  /s2 [c oc -> fc]. 
by apply/(s5 (osucc a) c ob oc) /oleSltP /(s6 _ _ oa oc).
Qed.

Definition first_derivation (f: fterm) := 
  (ordinalsf (fun z => ordinalp z /\ f z = z)).


Lemma first_derivation_p f (fp := first_derivation f): normal_ofs f ->
  ( (forall x, ordinalp x -> f (fp x) = fp x)  /\
    (forall y, ordinalp y  -> f y = y -> exists2 x, ordinalp x & y = fp x)).
Proof.
move => pa.
move:(iclosed_fixpoints pa).
pose p z :=(ordinalp z /\ f z = z).
have sa: (forall x, p x -> ordinalp x) by move => x [].
rewrite /fp /first_derivation -/p.
move => [sc sd].
move:(ordinals_col_p1 sa sd) => [pb pc pd pe [pf pg]].
by split; [move => x /pb [_] | move => y oy fy; apply:pc ].
Qed.

Lemma first_derivation_p0 (f: fterm): normal_ofs f ->
  normal_ofs (first_derivation f).
Proof.
move /iclosed_fixpoints => pa; exact: (ordinals_col_p2 pa).
Qed.

Lemma first_derivation_p1 f: normal_ofs f ->
  (first_derivation f \0o) = the_least_fixedpoint_ge f \0o.
Proof.
move => nf; move:(iclosed_fixpoints nf) => [pa pb].
set p  := (fun z => ordinalp z /\ f z = z).
have pc: forall x, p x -> ordinalp x by move=> x [].
move: (ordinals_col_p1 pc pb) => [q1 q2 q3 q4 [q5 q6]].
rewrite /first_derivation -/p.
move: (normal_ofs_fix nf OS0) => [sa sb sc].
apply: oleA.
  by move: (q2 _ (conj (proj32 sa)  sb)) => [a /ole0x aa ->]; apply: q3.
by move: (q1 _ OS0) => [ /ole0x ha hb]; apply: sc.
Qed.

Lemma first_derivation_p2 f: normal_ofs f -> f \0o <> \0o ->
  (first_derivation f \0o) = the_least_fixedpoint_ge f \1o.
Proof.
move => nf nf0; move:(iclosed_fixpoints nf) => [pa pb].
set p  := (fun z : Set => ordinalp z /\ f z = z).
have pc: forall x, p x -> ordinalp x by move=> x [].
move: (ordinals_col_p1 pc pb) => [q1 q2 q3 q4 [q5 q6]].
rewrite /first_derivation -/p.
move: (normal_ofs_fix nf OS1) => [sa sb sc].
apply: oleA.
  by move: (q2 _ (conj (proj32 sa)  sb)) => [a /ole0x oa ->]; apply: q3. 
move: (q1 _ OS0) => [ ha hb]; apply: sc => //;apply: oge1 => //.
by move => ba; case: nf0; rewrite - ba.
Qed.


Lemma first_derivation_p3 f x: normal_ofs f ->  ordinalp x ->
  (first_derivation f (osucc x)) = 
    the_least_fixedpoint_ge f (osucc (first_derivation f x)).
Proof.
move => nf ox; move:(iclosed_fixpoints nf) => [pa pb].
set p  := (fun z : Set => ordinalp z /\ f z = z).
have pc: forall y, p y -> ordinalp y by move=> y [].
move: (ordinals_col_p1 pc pb) => [q1 q2 q3 q4 [q5 q6]].
rewrite /first_derivation -/p.
move: (q1 _ ox) => [ta tb].
move: (normal_ofs_fix nf (OS_succ ta)) => [/oleSltP sa sb sc].
apply: oleA.
  move: (q2 _ (conj (proj32_1 sa) sb)) => [a oa av].
  case:(oleT_el oa ox); first by move/q3=> xx;case:(oltNge sa); rewrite av. 
  by rewrite av; move /oleSltP /q3.
move: (q1 _ (OS_succ ox)) => [ua ub];apply: sc => //; apply /oleSltP.
by apply: q4; apply: oltS.
Qed.

Lemma normal_ofs_from_exten f g : f =1o g -> normal_ofs f ->  normal_ofs g.
Proof.
move => h [sa sb].
split => //. 
  move => x y xy; move: (xy)=> [[ox oy _]_]. 
 by rewrite - h // - h //; apply: sa.
move => x lx; move:  (proj31 lx) => ox.
rewrite -(h x ox) (sb _ lx).
by apply: ord_sup_2funI => t /(Os_ordinal ox); apply: h.
Qed.

Lemma first_derivation_exten f g : f =1o g -> normal_ofs f ->
 first_derivation f =1o  first_derivation g.
Proof.
move => h osf.
have osg := (normal_ofs_from_exten h osf).
have [sa sb]:=(first_derivation_p osf).
have [sc sd] :=(first_derivation_p osg).
move: (first_derivation_p0 osf) (first_derivation_p0 osg) => [ia  _] [ib _].
apply: (sincr_ofs_exten ia ib).
+ move => x ox.
  have ha: ordinalp (first_derivation f x) by apply: ofs_sincr.
  by apply: sd => //;rewrite - h //;apply: sa.
+ move => x ox.
  have ha: ordinalp (first_derivation g x) by apply: ofs_sincr.
  by apply: sb => //;rewrite h //;apply: sc.
Qed.

Lemma first_derivation_p4 (f: fterm) C (E:= cnext C) (f' := first_derivation f)
   (F := Zo E (fun z => f z = z)):
   infinite_c C ->
   normal_ofs f ->
   (forall x, inc x E -> inc (f x) E) ->
   order_isomorphism (Lf f' E F) (ordinal_o E) (ole_on F).
Proof.
move => iC nf fse;move: (iC) => [cC _].
move:(cnext_pr1 cC); rewrite -/E; move=> [pa pb pc].
move: (iclosed_fixpoints nf)=> pab'.
move: (ordinals_col_p2 pab') => nf'.
set p  := (fun z => ordinalp z /\ f z = z).
have pc': forall x, p x -> ordinalp x by move=> x [].
move: (ordinals_col_p1 pc' (proj2 pab')). 
have -> : ordinalsf p = f' by [].
move => [q1 q2 q3 q4 [q5 q6]].
move: (proj1 pa) => oe.
have oes:= (Os_ordinal oe).
set g := Lf f' E F.
have sa: forall a b, inc b E -> a <o b -> inc a E.
  move => a b /(oltP oe) ha hb; apply/(oltP oe); apply:olt_ltT hb ha.
have lfa: lf_axiom f' E F.
  move => x xE; move: (oes _ xE) => ox; move:(q1 _ ox) => [_ aa].
  apply: Zo_i => //; clear aa.
  move: x ox xE;apply:least_ordinal2 => x ox xp xE.
  have ozz:= (oes _ xE).
  have ell: forall t, t <o x -> inc (f' t) E. 
    move => t ltx; apply: (xp _ ltx (sa _ _ xE ltx)).
  have H:= (next_fix_point_small iC nf fse).
  case: (ordinal_limA ox).
      move => ->; rewrite /f' (first_derivation_p1 nf); apply: H.
      apply cnextP => //; split;rewrite ? (card_card CS0); fprops.
      apply(cle0x cC).
    move => [t ot te]; rewrite te. 
    rewrite /f' (first_derivation_p3 nf ot); apply: H.
    by apply:(cnext_succ iC); apply: ell; rewrite te; apply: oltS.
  move => lz; move: (proj2 nf' _ lz). 
  set w := ordinalsf _ ; have -> : w = f' by []; clear w.
  move => ->; apply: (cnext_sup iC).
    move /(cnextP cC): xE => [_]; apply: cleT.
    exact: (fun_image_smaller x f').
  by move => t /funI_P [u /(oltP ox) uz ->]; apply:ell. 
split.
- apply: ordinal_o_or.
- apply: order_from_rel; apply:ole_order_r.
- split.
  + apply: lf_bijective.
   - done.
   - move => u v /oes ou /oes ov sv.
     by case: (oleT_ell ou ov) => // /q4 []; rewrite sv.
   - move => y /Zo_P [ye yv]; move: (q2 _ (conj (oes _ ye) yv)) => [a a1 a2].
     exists a => //; move: (osi_gex q4 a1); rewrite - a2.
     move /(oltP oe): ye => ha hb; apply/(oltP oe); apply:(ole_ltT hb ha).
  +  by rewrite ordinal_o_sr /g; aw. 
  +  by rewrite graph_on_sr /g ; aw; trivial => a /Zo_P [/oes /oleR oa _].
- hnf;rewrite /g;aw; move => x y xE yE; rewrite !LfV//; split.
    move /sub_gleP => [_ _ xy]; apply /graph_on_P1; split; fprops.
    apply: q3; split; fprops.
  move /graph_on_P1 => [_ _] /(q5 _ _ (oes _ xE) (oes _ yE)) [_ _  xy].
  by apply /sub_gleP. 
Qed.

Lemma ord_rev_pred x (y:= x -o \1o) : \0o <o x->
   (ordinalp y /\ x = \1o +o y).
Proof. by move /oge1P => /odiff_pr. Qed.

Lemma rev_pred_prop (f := osum2 \1o):
  normal_ofs f /\ (forall y, \0o <o y -> exists2 x, ordinalp x & y = f x).
Proof.
split; first apply: (osum_normal OS1).
by move => y /ord_rev_pred [pa pb]; exists (y -o \1o); rewrite /f.
Qed.

Lemma non_zero_ord_enum:
  (osum2 \1o) =1o ordinalsf (fun x => \0o <o x).
Proof.
set p := (fun x => \0o <o x).
have pa :(iclosed_proper p).
  split.
    split; first by  move => x [] [].
    move => F hx [t tx].
    have osf: ordinal_set F by move => x /hx [[] ].
    move: (ord_sup_ub osf tx); apply: olt_leT; exact (hx _ tx).
  apply: unbounded_non_coll => x ox; exists (osucc x); first exact:(oleS ox).
  by apply:olt0S.
apply:(normal_ofs_uniqueness (p:= fun z => z+o \1o)). 
- exact: (osum_normal OS1).
- exact: (ordinals_col_p2 pa).
- by move => x ox; rewrite - (osucc_pr ox) (osumA OS1 ox OS1).
- move => x /(iclosed_col_fs pa).
  set u := ordinalsf p x; set v := ordinalsf p (osucc x).
  rewrite /p;move =>[/oleSltP uv [[_ ou _] _] _ h].
  rewrite (osucc_pr ou); apply: oleA => //. 
  apply: h; [by apply:olt0S | by apply:oltS].
- move: (iclosed_col_f0 pa); set u := ordinalsf p \0o. 
  rewrite (osum0r OS1); move => [] /oge1P u1 h.
  exact: (oleA u1 (h _ olt_01)).
Qed.

Lemma add_fix_enumeration a: ordinalp a ->
  first_derivation (osum2 a) =1o (osum2 (a *o omega0)).
Proof.
move => oa.
set b := a *o omega0.
have ob: ordinalp b by apply: (OS_prod2 oa OS_omega).
move: (osum_normal oa) (osum_normal ob) => npa npb.
have pa:= (iclosed_fixpoints npa).
have na:=(ordinals_col_p2 pa).
apply:(normal_ofs_uniqueness (p:= fun z => z+o \1o)) => //.
    move => x ox.
    move: (iclosed_col_fs pa ox). 
    set u:= ordinalsf _ x; set v := ordinalsf _ (osucc x).
    move => [sa [ou sb] _ sc].
    move: (oltS ou) => h.
    rewrite osucc_pr //; apply: oleA; last by apply /oleSltP.
    by apply: (sc _ _ h); split; [ fprops | rewrite - (osum2_succ oa ou) sb].
  move => x ox; rewrite - osucc_pr // osumA //; fprops.
rewrite osum0r //.
rewrite (first_derivation_p1 npa) /the_least_fixedpoint_ge.
move: (induction_defined_pr (osum2 a) \0o).
set g := induction_defined _ _; move => [sg [fg sjg g0 gn]].
rewrite sg in sjg.
move: NS0 => bs0.
have gnn: forall n, natp n -> Vf g n = a *o n.
  apply: Nat_induction; first by rewrite oprod0r.
  move => n nb h. 
  rewrite (gn _ nb) h (oprod2_nsucc oa (OS_nat nb)) (osum2_2int NS1 nb).
  by rewrite (Nsucc_rw nb) csumC.
case: (ozero_dichot oa) => ap.
  suff: (target g) = singleton \0o by  move => ->; rewrite setU_1 /b ap oprod0l.
  apply: set1_pr; first by rewrite - g0; Wtac; rewrite sg. 
  by move => z /sjg [x /gnn xsg ->]; rewrite xsg ap  oprod0l.
move: (oprod_normal ap) => /normal_ofs_equiv1 [ha hb].
have ->: (target g) = (fun_image Nat (oprod2 a)).
  set_extens t; first by  move/sjg => [x xa ->]; apply /funI_P; ex_tac.
  move /funI_P => [z zN ->]; rewrite - (gnn _ zN); Wtac.
have bns:(forall x, natp x -> \0o <=o x) by move => x /OS_nat /ole0x.
have nex: nonempty Nat by exists \0c; apply: NS0.
by rewrite(hb _ bns nex) - [union _]omega_limit0.
Qed.

Lemma add1_fix_enumeration:
  first_derivation (osum2 \1o) =1o (osum2 omega0).
Proof.
by move => t ot; rewrite(add_fix_enumeration OS1 ot) (oprod1l OS_omega).
Qed.


Lemma omega_div x: ordinalp x -> 
  exists a b, [/\ ordinalp a, b<o omega0, x = omega0 *o a +o b &
     (osuccp x <-> b <> \0o)].
Proof.
move => ox; move: (oquoremP ox olt_0omega) => ha.
move: (ha) => [oq or xv ro].
exists (oquo x omega0), (orem x omega0).
have op: ordinalp (omega0 *o (oquo x omega0)) by fprops.
split => //;split.
  move => osx rz.
  move: osx; rewrite xv rz (osum0r op) => osx.
  move/(oprod_succP  OS_omega oq): osx => [so _].
  case:(limit_nonsucc' omega_limit so).
move => rz.
rewrite xv; apply/(osum_succP op or); right.
move/oltP0: ro => [_ _ rN].
move: (cpred_pr rN rz); set c := cpred _; move => [cN  ->].
rewrite (succ_of_nat cN); exists c => //; exact:(OS_nat cN).
Qed.

Lemma limit_ordinal_P4 x: ordinalp x ->
  (limit_ordinal x <-> exists2 y, \0o <o y & x = omega0 *o y).
Proof.
move => ox; split => h.
  move: (omega_div ox) => [a [b [oa ob dv etc]]].
  case: (equal_or_not b \0o) => bz.
    have xa: x = omega0 *o a by rewrite dv bz osum0r; fprops.
    case: (ozero_dichot oa) => az; last by exists a.
    by case: (limit_nz h); rewrite xa az oprod0r.
  by move /etc: bz => sp; case(limit_nonsucc' h sp).
move: h => [y [[_ oy _] ynz] ->].
move: OS_omega omega_limit => oo ol.
case: (ordinal_limA oy) => hx; first by case: ynz.
  move: hx => [z oz zv].
  rewrite zv (oprod2_succ oo oz); apply:osum_limit; fprops.
apply: oprod_limit => //; apply: olt_0omega.
Qed.

Lemma non_succ_ord_enum:
  (oprod2 omega0) =1o ordinalsf (fun x => ordinalp x /\ ~ (osuccp x)).
Proof.
set p := (fun x => ordinalp x /\ ~ (osuccp x)).
have p0: forall x, p x -> x = \0o \/ limit_ordinal x.
  by move => x [/ordinal_limA h pa]; case: h; fprops.
have p1: forall x, p x -> exists2 y, ordinalp y & x = omega0 *o y.
  move => x px; move: (px) => [ox _]; case: (p0 _ px).
    by move => ->; exists \0o; fprops; rewrite oprod0r.
  by move /(limit_ordinal_P4 ox) => [y [[_ oy _] _] yp]; exists y.
have p2: forall x, limit_ordinal x -> p x.
   move => x lx; split; [exact: (proj31 lx) | exact:(limit_nonsucc' lx)].
have pz: p \0o by split; fprops; move => [n on ns]; by case:(@osucc_nz n).
have p3: forall x, ordinalp x -> p (omega0 *o x).
  move => x ox; case: (ozero_dichot ox); first by move => ->;rewrite oprod0r.
  by move => xz; apply: p2; apply /limit_ordinal_P4; fprops; exists x.
have opp: ordinal_prop p by move => x [].
have p4 :(iclosed_proper p).
  split; first  split => // F fl nef.
    have os: ordinal_set F by move => x /fl [].
    case: (ord_sup_inVlimit os nef); [by move => /fl | apply: p2].
  apply:unbounded_non_coll => // x ox; exists(omega0 *o x); last by apply: p3.
  exact: (oprod_M1le olt_0omega ox).
move:olt_0omega  OS_omega => oo odo.
apply:(normal_ofs_uniqueness (p:= fun z => z +o omega0)). 
- apply: (oprod_normal oo).
- by apply: (ordinals_col_p2 p4).
- by move => x ox; rewrite oprod2_succ.
- move => x /(iclosed_col_fs p4).
  set u := ordinalsf p x; set v := ordinalsf p (osucc x).
  move => [uv pu pv h]; move: uv h; move/p1:pu => [a oa ->].
  move/p1:pv => [b ob ->]  /(oprod_Meqltr oa ob odo) => lab h.
  rewrite - (oprod2_succ odo oa); ex_middle bad.
  have ra := (oprod_Meqlt (oltS oa) oo).
  have rb := (p3 _ (OS_succ oa)).
  move: (oprod_Meqltr ob (OS_succ oa) odo (conj (h _ rb ra) bad)).
  by move /oltSleP => /(oltNge lab).
- move: (iclosed_col_f0 p4); set u := ordinalsf p \0o.
  by rewrite oprod0r; move => [_ h]; move: (h _ pz) => /ole0.
Qed.

(** **  Indecomposable ordinals *)

Definition indecomposable c :=
  \0o <o c /\ (forall a b, a <o c -> b <o c -> a +o b <> c).

Lemma OS_indecomposable a: indecomposable a -> ordinalp a.
Proof. move => h; exact: (proj32_1 (proj1 h)). Qed.

Lemma indecomp_pr c a b:
  ordinalp a -> ordinalp b ->
  indecomposable c -> a +o b = c -> (a = c \/ b = c).
Proof.
move => oa ob [_ oix] xs.
move: (osum_M0le oa ob)(osum_Mle0 oa ob).
rewrite xs => h1 h2.
case: (equal_or_not a c)=> lt2; first by left.
case: (equal_or_not b c)=> lt1; first by right.
by move: (oix _ _ (conj h2 lt2) (conj h1 lt1)). 
Qed.

Lemma indecomp_one: indecomposable \1o.
Proof.
split; [ by apply: olt_01 | move=> x y xo yo].
rewrite (olt1 xo) (olt1 yo) (osum0l OS0); fprops.
Qed.

Lemma indecomp_omega: indecomposable omega0.
Proof.
split; first exact: olt_0omega. 
by move=> x y xf yf; move: (osum2_lt_omega xf yf) => [_].
Qed.

Lemma cardinal_indecomposable x: infinite_c x ->  indecomposable x.
Proof.
move => xc; move: (proj1 xc) => cx.
split; first by exact:(ord_ne0_pos (proj1 cx) (infinite_nz xc)).
move => u v le1 le2 /(f_equal cardinal).
move: (proj31_1 le1) (proj31_1 le2) => ou ov.
rewrite osum_cardinal // (card_card cx) => /esym eq2.
move: le1 => /(ocle2P cx ou) lt1.
move: (csum_inf2 (CS_cardinal v) xc lt1 eq2) => h. 
by move: le2 => /(ocle2P cx ov) [_ []].
Qed.

Lemma indecomp_example x: \0o <o x ->
  ~ (indecomposable (osucc x)).
Proof.
move=> [[_ ox _] xnz']  [_ h2].
have p1:= (oltS ox).
have p2:= (ole_ltT (oge1 ox (nesym xnz')) p1).
case: (h2 _ _ p1 p2); rewrite osucc_pr //.
Qed.

Lemma indecomp_limit a: indecomposable a ->
   a = \1o \/ limit_ordinal a.
Proof.
move => oix.
have ox:= (OS_indecomposable oix).
case:(ordinal_limA ox); last by move=> lx; right.
  by move: oix => [[_ pa] _] xe; case: pa.
move=> [y oy ysx]; left; rewrite ysx.
case: (equal_or_not y \0o) => ynz; first by rewrite ynz osucc_zero.
by move: (indecomp_example (ord_ne0_pos oy ynz)); rewrite -ysx.
Qed.


Lemma indecomp_omega1 a: indecomposable a -> 
  a = \1o \/ omega0 <=o a.
Proof. 
by case /indecomp_limit => h; [ left | right; apply: limit_ge_omega].
Qed.

Lemma indecomp_prop1 c a: indecomposable c ->
  a <o c -> a +o c = c.
Proof.
move=> [_ oi]  ltac; move: (ltac) =>[leac _].
move: (odiff_pr leac) => [_ se]. 
case: (ole_eqVlt (odiff_Mle (proj31 leac) (proj32 leac))) => h.
  by rewrite {2} se h.
by move: (oi _ _ ltac h); rewrite - se.
Qed.


Lemma cardinal_indecomposable1 c a : infinite_c c -> a <o c -> 
  ((c -o a) = c /\ cardinal (c -s a) = c).
Proof.
move => icx ax; move: (icx) => [cx _].
move: (ax) => [[oa ox _] _].
have oix:= (cardinal_indecomposable icx).
have eq1:= (indecomp_prop1 oix ax).
move: (odiff_pr (proj1 ax)); rewrite - {2} eq1; move => [ob bv].
split; first by symmetry; exact:(osum2_simpl ox ob oa bv).
move /(ocle2P (proj1 icx) oa): ax; move: icx.
rewrite -{1 2 4} (card_card cx) => /infinite_setP; apply:infinite_compl.  
Qed.

Lemma indecomp_prop2 a b c: a <o c -> b <o c -> indecomposable c ->
    a +o b <o c.
Proof.
move => ac bc oic.
move: (proj31_1 ac) (bc) => oa [[ob oc _] _].
split; last exact: ((proj2 oic) _ _ ac bc).
rewrite -(indecomp_prop1 oic ac) -(indecomp_prop1 oic bc) osumA //.
apply:(osum_Mle0 (OS_sum2 oa ob) oc).
Qed.

Lemma indecompP c: \0o <o c  ->
  (indecomposable c <-> (forall a, a <o c -> a +o c = c)).
Proof.
move => cp; split; first by move => /indecomp_prop1.
move=> h; split=> // a b lt1 [lt2 ne2].
rewrite - (h _ lt1) => h1; case: ne2.
exact: (osum2_simpl (proj31 lt2) (proj32 lt2) (proj31_1 lt1) h1).
Qed.


Lemma indecomp_prodP x y: \1o <o x -> \0o <o y ->
  (indecomposable x <-> indecomposable (y *o x)).
Proof.
move=> cx1 cy0.
move: (proj32_1 cx1)  (proj32_1 cy0) => ox oy.
move: (olt_leT olt_01 (proj1 cx1)) => xp.
split; last first.
  move=> [ha hb]; split => //; move=> a b ax bx.
  move: (oprod_Meqlt ax cy0) => lt1.
  move: (oprod_Meqlt bx cy0) => lt2.
  move: (proj31_1 ax)  (proj31_1 bx) => oa ob.
  move: (hb _ _ lt1 lt2); rewrite - oprodD //.
  by move=> h1; dneg h2;rewrite h2.
move=> xi.
move: (OS_prod2 oy ox) OS1 => op io1.
have xynz: \0o <o y *o x by apply: oprod2_pos.
apply/(indecompP xynz) => z ltz.
have oz: ordinalp z by move: ltz => [[oz _]_].
move: (odivision_exists oy ox ltz)=> [[oq or zv ltrq] ltry].
apply: oleA; last by apply: osum_M0le.
rewrite - {2} (indecomp_prop1 xi ltry) -{2} (indecomp_prop1 xi cx1) osumA //.
rewrite (oprodD (OS_sum2 oq OS1) ox oy) {1} zv (oprodD oq OS1 oy).
apply:(osum_Mleeq _ (proj32_1 xynz)); apply:(osum_Meqle _ (OS_prod2 oy oq)). 
rewrite (oprod1r oy); exact: (proj1 ltrq).
Qed.

Lemma indecomp_div x y: indecomposable x ->
  y <> \0o -> y <o x ->
  exists z, [/\ indecomposable z, ordinalp z &  x = y *o z].
Proof.
move=> oix ynz ltyx.
move: (ltyx) => [[oy ox _] _].
have yp:= (ord_ne0_pos oy ynz).
move: (oquoremP ox yp) => [oq or /esym xeq [lt1 _]].
move:(proj2(ole_ltT lt1 ltyx)) => xnr.
case: (ozero_dichot oq) => qz.
  by move: xnr; rewrite -{2} xeq qz oprod0r (osum0l or).
case: (indecomp_pr (OS_prod2 oy oq) or oix xeq) => ea //.
exists (oquo x y); split => //.
case: (oone_dichot qz) => q1; first by rewrite q1; apply: indecomp_one.
apply/(indecomp_prodP q1 yp); ue.
Qed.

Lemma indecomp_diff1 c a: indecomposable c -> a <o c -> c -o a = c.
Proof.
move =>ic [leac nac].
move: (odiff_pr leac)=> [od dv].
by case: (indecomp_pr (proj31 leac) od ic (esym dv)).
Qed.

Lemma indecomp_diff2 c: \0o <o c  ->
  (forall a,  a <o c -> c -o a = c) ->indecomposable c.
Proof.
move => oc cp. apply/(indecompP oc) => a lac.
by rewrite -{1} (cp _ lac) -(proj2 (odiff_pr (proj1 lac))).
Qed.

  




Lemma indecomp_prod2 a (b:= a *o omega0): \0o <o a ->
  [/\ indecomposable b, a <o b &
  forall c, indecomposable c -> a <o c -> b <=o c].
Proof.
move=> ap.
have oa:= proj32_1 ap.
have anz:= (nesym (proj2 ap)).
have o1: \1o <o omega0 by apply /olt_omegaP; fprops.
split; first by move /(indecomp_prodP o1 ap) : indecomp_omega.
  apply:(oprod_Meq1lt o1 ap).
move=> c oic ac.
move: (indecomp_div oic anz ac) => [z [oiz oz xp]].
rewrite /b xp; apply: (oprod_Mlele (oleR oa)).
case: (indecomp_omega1 oiz) => // z1.
move: xp; rewrite z1 oprod1r// => ca.
by move: ac => [_]; rewrite ca. 
Qed.

Lemma indecomp_prod3 a: \0o <o a ->
   (osucc a) *o omega0 = a *o omega0.
Proof.
move=> ap.
have oa:= (proj32_1 ap).
move: (olt0S oa) => sp.
move: (indecomp_prod2 ap) (indecomp_prod2 sp).
set (x := (osucc a) *o omega0); set (y:= a *o omega0).
move  => [p1 p2 p3] [q1 q2 q3].
apply: oleA; last by apply: (p3 _ q1);apply /oleSltP;move: q2=> [ok _].
apply: (q3 _ p1);  split; first by apply /oleSltP.
by move=> h; move: (indecomp_example ap);rewrite h.
Qed.

Lemma indecomp_sup E: 
  (forall x, inc x E -> indecomposable x) ->
  (nonempty E) ->
  indecomposable (\osup E).
Proof.
move => ai [w wE].
have osE: ordinal_set E by move => t /ai [/proj32_1 h _].
move: (ord_sup_ub osE wE); set x := \osup E => wx.
have xp:= (olt_leT (proj1 (ai _ wE)) wx).
split=> // a b /(olt_sup osE)[a' a'E aa'] /(olt_sup osE) [b' b'E bb'].
move:(omax_p1 (proj32_1 aa') (proj32_1 bb'));set z := omax a' b'.
move => [za zb].
have zE: inc z E by  apply: Gmax_E.
have az := olt_leT aa' za.
have bz := olt_leT bb' zb.
move => abx; move: (ord_sup_ub osE zE); rewrite -/x -abx => l1.
case: (oleNgt l1 (indecomp_prop2 az bz (ai _ zE))).
Qed.

Lemma indecomp_sup1 x: \0o <o x ->
  exists y, [/\ indecomposable y, y <=o x &
    forall z, indecomposable z -> z <=o x -> z <=o y].
Proof.
move=> xp.
have ox:=proj32_1 xp.
set E := Zo (osucc x) indecomposable.
have pa: (forall t, inc t E -> indecomposable t) by move =>t /Zo_P [_].
have pb: nonempty E. 
  exists \1o; apply:Zo_i; last by apply:indecomp_one.
  move /oltSSP: xp => /(oltP (OS_succ ox)).
  by rewrite osucc_zero.
have pc: (forall t, inc t E -> t <=o x) by move =>t /Zo_P [] /(oleP ox).
have osE: ordinal_set E by move => t  /pc [].
move: (ord_sup_ub osE)(OS_sup osE) (ord_ub_sup ox pc) => pe pf pg.
move: (indecomp_sup pa pb) => h; exists (\osup E); split => // z za zx.
by apply: pe; apply: Zo_i =>//; apply /(oleP ox).
Qed.

Lemma indecomp_closed_noncoll: iclosed_proper indecomposable.
Proof.
move: indecomp_sup => h.
have ha: ordinal_prop indecomposable by move => x [/proj32_1 xp _].
split => // [] [E ep].
have ose: ordinal_set E by move => x /ep [/proj32_1 xp _].
move: (OS_sup ose) => os; move: (OS_succ os)=> oy.
have yp: \0o <o osucc (union E) by apply: olt0S.
move: (indecomp_prod2 yp); set z := _ *o _; move => [sa sb sc].
case: (oltNge (olt_leT (oltS os) (proj1 sb))).
by apply:(ord_sup_ub ose); apply/ ep.
Qed.

(** ** Definition by induction  for the exponential *)

Definition ord_induction_sup (g: fterm2) x y (fx: fterm) :=
  \osup (fun_image y (fun z => g (fx z) x)).

Lemma ord_induction_unique (w0: fterm)  (g:fterm2) u (f f':fterm2)
  (P := fun f => forall x, u <=o x ->
   ( f x \0o = w0 x /\
    (forall y, \0o <o y -> f x y = ord_induction_sup g x y (f x)))):
  P f -> P f' ->  forall x, u <=o x -> f x =1o f' x.
Proof.
move => pa pb x ux; apply:least_ordinal2 => y oy lpy.
move: (pa _ ux)  (pb _ ux) => [h1 h2] [h3 h4].
case: (ozero_dichot oy) => ey0; first by rewrite ey0 h1. 
rewrite (h2 _ ey0)(h4 _ ey0).
by apply: ord_sup_2funI => z /(oltP oy) /lpy ->.
Qed.

Definition ord_induction_p (w0:fterm) (g:fterm2) x F :=
  (Yo (domain F = \0o) (w0 x) (ord_induction_sup g x (domain F) (Vg F))).
 
Definition ord_induction_defined (w0:fterm) (g:fterm2) x :=
   transdef_ord (ord_induction_p w0 g x).

Lemma ord_induction_y0 w0 g x:
  ord_induction_defined w0 g x \0o = w0 x.
Proof.
rewrite /ord_induction_defined (transdef_ord_pr (ord_induction_p w0 g x) OS0).
by rewrite /ord_induction_p; aw; Ytac0.
Qed.

Lemma ord_induction_yp w0 g x (f:= (ord_induction_defined w0 g)):
    (forall y, \0o <o y -> f x y = ord_induction_sup g x y (f x)).
Proof.
move => y [[_ oy _] ynz].
rewrite /f /ord_induction_defined. 
rewrite (transdef_ord_pr (ord_induction_p w0 g x) oy).
rewrite /transdef_ord_prop {1} /ord_induction_p; aw; Ytac0. 
apply: ord_sup_2funI => t ty /=; rewrite LgV//.
Qed.


Lemma ord_induction_y1 w0 g x:
  ord_induction_defined w0 g x \1o = g (w0 x) x.
Proof.
rewrite (ord_induction_yp _ _ _ olt_01).
by rewrite /ord_induction_sup funI_set1 setU_1 ord_induction_y0. 
Qed.


Section OrdinalInduction.
Variables (u: Set) (w0: fterm) (f g : fterm2). 
Hypothesis fv: f = ord_induction_defined w0 g.

Let w1 := fun x => (g (w0 x) x).
Definition OIax_w0 := forall x, u <=o x -> w0 x <o w1 x.
Definition OIax_w1 := forall x, u <=o x -> x <=o w1 x.
Definition OIax_g1 := forall x y, u <=o x -> u <=o y -> x <o (g x y).
Definition OIax_g2:= forall a b a' b',
    u <=o a -> u <=o b ->  a <=o a' -> b <=o b' -> 
   (g a b) <=o (g a' b').
Definition OIax_w2w:= forall a a', u <=o a -> a <=o a' -> (w0 a) <=o (w0 a').
Definition OIax_w2:= forall a a', u <=o a -> a <o a' -> w1 a <o w1 a'.
Definition OIax_w3:= forall a, u <=o a -> w1 a = a.
Definition OIax_g3:= forall a, u <=o a -> normal_ofs1 (fun b => g a b) u.
Definition OIax_g4:= forall a b c, u <=o a -> u <=o b -> u <=o c ->
     g (g a b) c = g a (g b c).

Definition OIax1 := [/\ OIax_w0, OIax_w1 & OIax_g1].
Definition OIax1b := OIax1 /\ OIax_g2.
Definition OIax2 := [/\ OIax1,  OIax_g2, OIax_w2w & OIax_w2].
Definition OIax3 := [/\ OIax2, OIax_w3, OIax_g3 & OIax_g4].

Lemma ord_induction_p01 x: OIax1 -> u <=o x -> f x \0o <o f x \1o.
Proof.
by move => [h _ _] ux; rewrite fv ord_induction_y0 ord_induction_y1; apply:h.
Qed.

Lemma ord_induction_p4 x y: OIax1 ->
  u <=o x -> \0o <o y -> x <=o (f x y).
Proof.
move=> [_ aw1 ag1] ux0 loy0; ex_middle npy0.
move: (least_ordinal5 loy0 npy0 (p:= fun z => x <=o (f x z))) => /=.
set z := least_ordinal _ _; move=> [oz z1 npz lpy];case: npz.
move: (aw1 _ ux0) => le1.
case: (oone_dichot z1) => x3; first by rewrite x3 fv ord_induction_y1.
rewrite fv  (ord_induction_yp w0 g x z1) - fv /ord_induction_sup.
set T:= fun_image _ _.
have oT: ordinal_set T.
  apply:Os_funI => w wc.
  have ow:= (Os_ordinal oz wc).
  case: (ozero_dichot ow) => wz.
    rewrite wz fv ord_induction_y0;  exact (proj32 le1).
  have /lpy le2: inc w (ordinal_interval \1o z).
     apply /(ointv1 oz); split => //; by apply/(oltP oz).
  exact: (proj32_1 (ag1 _ _ (oleT ux0 le2) ux0)).
have iz1: inc \1o z by apply/(oltP oz).
have sT: inc (g (f x \1o) x) T by apply /funI_P; ex_tac.
have r1:= (ord_sup_ub oT sT).
have ww: x <=o f x \1o by rewrite fv ord_induction_y1; apply: (aw1 _ ux0).
exact: (oleT (oleT ww (proj1 (ag1 _ _ (oleT ux0 ww) ux0))) r1).
Qed.

Lemma ord_induction_p41 x y: OIax1 -> 
  u <=o x -> \0o <o y -> u <=o (f x y).
Proof.
move=> ax1 ux y1; exact: (oleT ux (ord_induction_p4 ax1 ux y1)).
Qed.

Lemma ord_induction_p5 x y: OIax1 ->
  u <=o x -> ordinalp y -> ordinalp (f x y).
Proof. 
move=> ax1 ux oy; case: (ozero_dichot oy) => y1.
  by move: (ord_induction_p01 ax1 ux); rewrite y1; move => [[]].
exact: (proj32 (ord_induction_p4 ax1 ux y1)).
Qed.

Lemma ord_induction_p6 x y: OIax1 ->
  u <=o x -> ordinalp y -> ordinalp (g (f x y) x).
Proof.
move => ax1 ux oy; case: (ozero_dichot oy) => y1.
  by move: (proj31 ax1 _ ux) => /proj32_1; rewrite y1 fv ord_induction_y0.
move: (ord_induction_p41 ax1 ux y1) => h1.
exact: (proj32_1(proj33 ax1 _ _ h1 ux)). 
Qed.

Lemma ord_induction_p7 x y y': OIax1 ->
  u <=o x -> y <o y' -> g (f x y) x <=o (f x y').
Proof.
move=> ax1 ux yz.
have [[oy oy' _] _] := yz.
have yp:= (ole_ltT (ole0x oy) yz).
rewrite fv (ord_induction_yp w0 g x yp) -fv. 
rewrite /ord_induction_sup;set T:= fun_image _ _.
have oT: ordinal_set T.
  by move => z /funI_P [v /(Os_ordinal oy') vz ->]; apply: ord_induction_p6. 
have iyy:inc y y' by apply/(oltP oy').
apply: (ord_sup_ub oT); apply /funI_P;ex_tac.
Qed.

Lemma ord_induction_p8 x y y': OIax1 ->
  u <=o x -> y <o y' ->  (f x y) <o (f x y').
Proof.
move=> ax1 ux yz.
wlog: y yz / \0o <o y => yp.
  case: (ozero_dichot (proj31_1 yz)) => y1; last by apply: yp.
  move: (ord_induction_p01 ax1 ux) => cp.
  case: (oone_dichot yz)=> y'1; first by rewrite y1 y'1; apply: cp.
  by move: (ole_ltT (proj1 cp) (yp _ y'1 olt_01)); rewrite y1.
have le1:= (ord_induction_p7 ax1 ux yz).
have le2:= (ord_induction_p41 ax1 ux yp).
exact: (olt_leT (proj33 ax1 _ _ le2 ux) le1). 
Qed.

Lemma ord_induction_p9 x y: OIax1 ->
  u <=o x -> ordinalp y -> y <=o (f x y).
Proof.
move=> ax1 ux; move: y; apply: least_ordinal2 => t ot lpy.
case: (ozero_dichot ot).
  move => ->; exact:(ole0x (proj31_1 (ord_induction_p01 ax1 ux))).
move => tp.
have orf: ordinalp (f x t) by apply: ord_induction_p5.
case: (oleT_el ot orf)=> // p3z. 
case:(oleNgt (lpy _ p3z) (ord_induction_p8 ax1 ux p3z)).
Qed.

Lemma ord_induction_p10 x: OIax1 ->
  u <=o x -> normal_ofs (f x).
Proof.
move=> ax1 ux; split.
  move => y y'; apply:(ord_induction_p8 ax1 ux).
move => a la. 
rewrite fv  (ord_induction_yp w0 g x (limit_pos la)) -fv.
apply: ord_sup_2cofinal; split => b /funI_P [z za ->].
  move: la => [pa pb pc]; move: (pc _ za) => sza.
  exists (f x (osucc z)); first by apply/funI_P;ex_tac.
  apply: (ord_induction_p7 ax1 ux); apply: (oltS (Os_ordinal pa za)).
move: la => [pa pb pc].  
have oz:=(Os_ordinal pa za).
exists (g (f x z) x); first by apply/funI_P; exists z.
case: (ozero_dichot oz) => aa.
  rewrite aa fv ord_induction_y0; exact (proj1 (proj31 ax1 _ ux)).
exact (proj1 (proj33 ax1 _ _ (ord_induction_p41 ax1 ux aa) ux)).
Qed.

Lemma ord_induction_p11 x b y y': OIax1 ->
  u <=o x -> ordinalp y -> ordinalp y' ->
  (f x y) <=o b -> b <o (f x (osucc y))  ->
  (f x y') <=o b -> b <o (f x (osucc y'))  ->
  y = y'.
Proof.
move=> ax1 ux.
have h: sincr_ofs (f x) by move => t t';apply:(ord_induction_p8 ax1 ux).
apply: (sincr_bounded_unique h).
Qed.

Lemma ord_induction_p12 x b: OIax1 ->
  u <=o x -> (w0 x) <=o b ->
  exists y,  [/\  y <=o b, (f x y) <=o b & b <o (f x (osucc y))]. 
Proof.
move=> ax1 ux w1b.
have ob:= proj32 w1b. 
case:(normal_ofs_bounded ob (ord_induction_p10 ax1 ux)).
  by rewrite fv ord_induction_y0 => /(oleNgt w1b).
move => [y [py pa pb]]; exists y; split => //.
exact (oleT (ord_induction_p9 ax1 ux py) pa).
Qed.

Lemma ord_induction_p13 x y: OIax1b ->
  u <=o x -> ordinalp y -> f x (osucc y) =  g (f x y) x.
Proof.
move=> [ax1 ax2] ux oy.
move: (OS_succ oy) => osy.
have ysy:= oltS oy.
apply: oleA; last by apply: ord_induction_p7.
have syp: \0o <o osucc y by apply /oltSleP; apply: ole0x. 
rewrite fv (ord_induction_yp w0 g x syp) -fv.
apply: ord_ub_sup.
  by apply:(ord_induction_p6 ax1 ux oy).
move => t /funI_P [s zsa ->].
case /setU1_P: zsa; last first.
  by move => ->; apply:oleR; apply:ord_induction_p6.
move => /(oltP oy) => sy.
have ox:= (proj32 ux).
wlog: s sy / \0o <o s => sp.
  have [aux _]: g (f x \0c) x <o g (f x \1c) x.
    rewrite fv ord_induction_y0 ord_induction_y1.
    apply: (proj33 ax1 _ _  _ ux); exact: (oleT ux (proj32 ax1 _ ux)).
  case: (ozero_dichot (proj31_1 sy)); last by apply:sp.
  move ->; case: (oone_dichot sy)=> yp; first by rewrite yp. 
  apply: (oleT aux (sp _ yp olt_01)).
move: (ord_induction_p41 ax1 ux sp) => pa.
apply: ax2 => //; [exact (proj1 (ord_induction_p8 ax1 ux sy))| fprops].
Qed.

Definition ord_induction_g_unit c :=
  [/\ ordinalp c, g c c = c, c = w0 c &
    forall x, u <=o x -> [/\ g x c = x, g c x = x & w0 x = c]].

Lemma ord_induction_zv c: ord_induction_g_unit c ->  OIax1 ->
  [/\  (forall a, u <=o a -> (g (w0 a) a) = a),
      (forall a b, u <=o a -> ordinalp  b ->
       f a (b +o \0o) = g (f a b) (f a \0o)),
   (forall a b, u <=o a -> ordinalp b ->
      f a (\0o +o b) = g (f a \0o) (f a b)),
   forall a b, u <=o a -> ordinalp b ->  f a (b *o \0o) = f (f a b) \0o &
   forall a b, u <=o a -> ordinalp b ->  f a (\0o *o b) = f (f a \0o) b].
Proof.
move => [oc gcc cwc h] ax1.
have pa: forall a, u <=o a -> f a \0o = c.
  by move => a au; rewrite fv  ord_induction_y0 (proj33 (h _ au)).
split.
- by move => a au; move: (h _ au) => [h1 h2 ->].
- move => a b ua ob.
  rewrite (osum0r ob) (pa _ ua).
  case: (ozero_dichot ob); first by move => ->;rewrite (pa _ ua).
  by move => bp; move: (h _  (ord_induction_p41 ax1 ua bp)) => [ -> _ _].
- move => a b ua ob.
  rewrite (osum0l ob) (pa _ ua).
  case: (ozero_dichot ob); first by move => ->;rewrite (pa _ ua).
  by move => bp; move: (h _  (ord_induction_p41 ax1 ua bp)) => [ _ ->  _].
- move => a b ua ob; rewrite oprod0r (pa  _ ua).
  case: (ozero_dichot ob). 
    by move => ->; rewrite (pa  _ ua) fv ord_induction_y0 - cwc.
  by move => bp; rewrite (pa _ (ord_induction_p41 ax1 ua bp)).
- move => a b ua ob.
  rewrite oprod0l (pa  _ ua) fv.
  move: b ob; apply: least_ordinal2  => y oy etc.
  move:  (ord_induction_y0  w0 g c) => g0.
  case: (ozero_dichot oy); first by move => ->; rewrite g0. 
  move => yp; rewrite (ord_induction_yp w0 g _ yp).
  rewrite / ord_induction_sup; set G := fun_image _ _.
  suff: G = singleton c by move => ->; rewrite setU_1.
  apply: set1_pr. 
    by apply /funI_P;exists \0o; [ apply:olt_i |rewrite g0 - cwc  gcc].
  by move => z /funI_P [t /(oltP oy) /etc <- ->].
Qed.


End OrdinalInduction.


Lemma ord_induction_p14
  (f:= ord_induction_defined id (fun u v:Set => osucc u)):
  (forall a b, ordinalp a -> ordinalp b -> f a b  = a +o b)
  /\ (forall a b c, ordinalp a -> ordinalp b -> ordinalp c ->
     f (f a b) c = f a (f b c)).
Proof.
pose w0 (x:Set) := x; pose g u (v:Set) :=  osucc u.
move: (erefl f) => ee.
have H: forall u,  \0o <=o u -> u <o osucc u.
  move => x [_ ox _]; exact (oltS ox).
have ax1: OIax1 \0o w0 g.
  rewrite /w0 /g;split.
  - by move => x /H xp.
  - by move => x /H [].
  - by move => u v /H up.
have ax2:OIax_g2 \0o g by move => u v x y _ _ /oleSSP uv _.
have aux: forall a, ordinalp a -> forall b, ordinalp b ->
   f a (osucc b) = osucc (f a b).
  move => a /ole0x oa nb ob.
  by rewrite (ord_induction_p13 ee (conj ax1 ax2) oa ob).
have f0: forall a, ordinalp a -> f a \0o = a +o \0o 
   by move => a oa; rewrite /f (ord_induction_y0 w0 g a) osum0r.
split. 
  move => a b oa ob.
  have ap:= ole0x oa.
  move: (ord_induction_p10  ee ax1 ap) => nfa.
  have pa: (forall x, ordinalp x -> f a (osucc x) = osucc (f a x)).
    by move => x /(aux _ oa).
  have pb:(forall x, ordinalp x -> a +o osucc x = osucc (a +o x)).
    by move => x ox; rewrite osum2_succ.
  have pc: f a \0o = a +o \0o by apply: f0.
  move: (normal_ofs_uniqueness nfa (osum_normal oa) (p:=osucc) pa pb pc).
  by apply.
move => a b c oa ob oc.
have ap:= ole0x oa.
have bp:= ole0x ob.
have hh: ordinalp (f a b) by apply:(ord_induction_p5 ee ax1 ap ob).
have qa: normal_ofs (fun c => f (f a b) c). 
   apply: (ord_induction_p10 ee ax1 (ole0x hh)).
have qb: normal_ofs (fun c => f a (f b c)).
  by apply:normal_ofs_compose; apply: (ord_induction_p10 ee ax1). 
have qc: forall x, ordinalp x -> f (f a b) (osucc x) = osucc (f (f a b) x).
  by move => x ox; rewrite aux.
have qd:forall x, ordinalp x -> f a (f b (osucc x)) = osucc (f a (f b x)).
  by move => x ox; rewrite aux // aux //; apply:(ord_induction_p5 ee ax1). 
have qe: f (f a b) \0o = f a (f b \0o) by rewrite f0 // f0 // osum0r // osum0r.
exact: (normal_ofs_uniqueness qa qb qc qd qe oc). 
Qed.


Lemma ord_induction_p15 a b:
  \0o <o a -> ordinalp b ->
  ord_induction_defined (fun z:Set=> \0o) osum2 a b = a *o b.
Proof.
move => oa ob.
set w0 := (fun _ : Set => \0o).
have ax1: OIax1 \1o w0 osum2.
  rewrite /w0;split.
  - move => x xp /=;rewrite osum0l; [ by apply/oge1P | exact: (proj32 xp)].
  - move => x [_ xp _] /=; rewrite osum0l;fprops.
  - move => u v [_ ou _] /oge1P vp. 
    by move: (osum_Meqlt vp ou); rewrite  osum0r.
have ax2:OIax_g2 \1o osum2  by move => u v x y /= _ _; apply:osum_Mlele.
set f := (ord_induction_defined w0 osum2).
have ap: \1o <=o a by apply/oge1P.
move: (ord_induction_p10 (erefl f) ax1 ap) => nfa.
pose p := fun x => x +o a.
have pa: (forall x, ordinalp x -> f a (osucc x) = p((f a x))).
  move => x ox; exact: (ord_induction_p13 (erefl f) (conj ax1 ax2) ap ox).
have pb:(forall x, ordinalp x -> a *o osucc x = p (a *o x)).
  by move => x ox; rewrite (oprod2_succ (proj32 ap)).
have pc: f a \0o = a *o \0o 
  by rewrite /f (ord_induction_y0 w0 osum2 a) oprod0r.
by apply: (normal_ofs_uniqueness nfa (oprod_normal oa) pa pb pc).
Qed.



Section OrdinalInduction2.
Variables (u: Set) (w0: fterm) (f g : fterm2). 
Hypothesis fv: f = ord_induction_defined w0 g.

Lemma ord_induction_p16 x y x' y': OIax2 u w0 g ->
  u <=o x -> x <=o x' ->  y <=o y' -> f x y <=o f x' y'.
Proof.
move=> [ax1 ag2 aw2w aw2] ux xx' yy'.
have ux':= oleT ux xx'.
have oy:= proj31 yy'.
apply: (@oleT (f x' y)); last first.
  apply: (sincr_incr _ yy')=> z z'; apply:(ord_induction_p8 fv ax1 ux').
apply:(least_ordinal2 (p:= fun y=> (f x y) <=o (f x' y))) oy => t ot lpy.
case: (ozero_dichot ot) => tp.
  by rewrite tp fv ord_induction_y0 ord_induction_y0; apply:aw2w.
rewrite fv (ord_induction_yp w0 g _ tp)(ord_induction_yp w0 g _ tp).
rewrite /ord_induction_sup.
set T1:= fun_image _ _; set T2:= fun_image _ _.
have oT1: ordinal_set T1.
  move=> v => /funI_P [w /(Os_ordinal ot) ow ->].
  rewrite - fv;apply:(ord_induction_p6 fv ax1 ux ow).
have oT2: ordinal_set T2.
  move=> v => /funI_P [w /(Os_ordinal ot) ow ->].
  rewrite - fv;apply:(ord_induction_p6 fv ax1 ux' ow).
have osT2:= (OS_sup oT2).
apply: (ord_ub_sup osT2).
move=> i => /funI_P  [z /(oltP ot) zt ->]; rewrite - fv.
have z2:= (olt_i zt).
have oz:= proj31_1 zt.
move: (lpy _ zt) => h1.
set j :=g (f x' z) x'. 
have jT2: inc j T2 by apply /funI_P ;exists z => //; rewrite - fv.
apply:(oleT _ (ord_sup_ub oT2 jT2)).
case: (equal_or_not x x') => exx'.
  by rewrite /j - exx'; apply:oleR; apply: (ord_induction_p6 fv ax1 ux).
case: (ozero_dichot oz) => zz. 
 rewrite /j zz fv ! ord_induction_y0; exact(proj1(aw2 _ _ ux (conj xx' exx'))).
by apply: ag2=> //; apply: (ord_induction_p41 fv ax1).
Qed.

Lemma ord_induction_p17 x x' y: OIax2 u w0 g ->
   (forall a b b', u <=o a -> u <=o b -> b <o b' -> g a b <o g a b') ->
   u <=o x -> x <o x' -> ordinalp y ->
   f x (osucc y) <o f x' (osucc y).
Proof.
move=> ax2 gsi ux xx' oy.
have lexx':= (proj1 xx').
have lexx:= (oleR (proj32 ux)).
have ux':= (oleT ux lexx').
have lt1:= (ord_induction_p16  ax2 ux lexx' (oleR oy)).
move: (ax2) => [ax1 ag2 aw2w aw2].
case: (equal_or_not y \0o) => yz.
  rewrite yz osucc_zero.
  rewrite fv ! ord_induction_y1; apply: aw2=> //.
have y1:= (ord_ne0_pos oy yz).
have h3:= (ord_induction_p41 fv ax1 ux y1).
have le2: (g (f x y) x) <=o (g (f x' y) x) by apply: ag2.
have lt3:(g (f x' y) x) <o (g (f x' y) x') by apply :gsi  (oleT h3 lt1) ux xx'.
have le4:= (ole_ltT le2 lt3).
rewrite (ord_induction_p13 fv (conj ax1 ag2) ux oy).
by rewrite (ord_induction_p13 fv (conj ax1 ag2) ux' oy).
Qed.


Lemma ord_induction_p18 a b c: OIax3 u w0 g ->
  u <=o a -> \0o <o b -> \0o <o c ->
    f a (b +o c) = g (f a b) (f a c).
Proof.
move => [[ax1 ag2 aw2w aw2] aw3 ag3 ag4] ua b1 /oge1P c1.
pose p y := g y a.
pose F1 c := f a (b +o c).
pose F2 c := g (f a b) (f a c).
have ufab : u <=o f a b by  apply: (ord_induction_p41 fv ax1).
have ob:=proj32_1 b1.
set ax3:= conj ax1 ag2.
move: (ord_induction_p10 fv ax1 ua) => na.
have pu: (forall x, \1o <=o x -> F2 (osucc x) = p (F2 x)).
  move => x /oge1P xp.
  rewrite /F2 (ord_induction_p13 fv ax3 ua (proj32_1 xp)) /p ag4 //.
  by apply: (ord_induction_p41 fv ax1).
have pv: (forall x, \1o <=o x -> F1 (osucc x) = p (F1 x)).
  move => x [_ ox _]; rewrite /F1 - (osum2_succ ob ox).
 rewrite (ord_induction_p13 fv ax3 ua) //; fprops.
have pa: normal_ofs1 F1 \1o.
  move: na => /normal_ofs_equiv1 n1.
  have bp:  \0o <=o b +o \1o by apply: ole0x; fprops.
  apply: (normal_ofs_compose1 OS0 OS1 bp n1).
  apply: (normal_ofs_equiv2 OS1); by apply: osum_normal.
have pb: normal_ofs1 F2 \1o. 
  move: (ag3 _ ufab) => ea.
  have uf1 : u <=o f a \1o by apply:(ord_induction_p41 fv ax1 ua olt_01).
  apply:(normal_ofs_compose1 (proj31 ua) OS1 uf1 ea).
  by apply: (normal_ofs_equiv2 OS1).
have pe: F1 \1o = F2 \1o. 
  rewrite /F1 /F2 (osucc_pr ob) (ord_induction_p13 fv ax3 ua ob).
  by move: (aw3 _ ua); rewrite -  (ord_induction_y1 w0 g a) - fv => ->.
exact:(normal_ofs_uniqueness1 pa pb OS1 pv pu pe c1).
Qed.

Lemma ord_induction_p19 a b c: OIax3 u w0 g ->
  u <=o a -> \0o <o b -> \0o <o c -> f a (b *o c) = f (f a b) c.
Proof.
move=> ax3 ua b1 /oge1P c1.
move:(ax3) => [[ax1 ag2 aw2w aw2] aw3 ag3 ag4].
pose p y := g y (f a b).
pose F1 c := f a (b *o c).
pose F2 c := f (f a b) c.
have ufab : u <=o f a b by apply: (ord_induction_p41 fv ax1).
have ob := proj32_1 b1.
have pu: (forall x, \1o <=o x -> F2 (osucc x) = p (F2 x)).
  by move=> x [_ xp _];rewrite /F2(ord_induction_p13 fv (conj ax1 ag2) ufab xp).
have pv: (forall x, \1o <=o x -> F1 (osucc x) = p (F1 x)).
  move => x /oge1P xp; rewrite /F1 (oprod2_succ ob (proj32_1 xp)).
  by rewrite ord_induction_p18 //; apply: oprod2_pos.
have pa: normal_ofs1 F1 \1o. 
  have bp:= ole0x (OS_prod2 ob  OS1).
  move: (ord_induction_p10 fv ax1 ua) => /normal_ofs_equiv1 n1.
  apply: (normal_ofs_compose1 OS0 OS1 bp n1); apply: (normal_ofs_equiv2 OS1).
  by apply: oprod_normal.
have pb: normal_ofs1 F2 \1o. 
  apply: (normal_ofs_equiv2 OS1); apply:(ord_induction_p10 fv ax1 ufab). 
have pe: F1 \1o = F2 \1o. 
  by rewrite /F1 /F2 (oprod1r ob) {2} fv  ord_induction_y1 (aw3 _ ufab).
exact:(normal_ofs_uniqueness1 pa pb OS1 pv pu pe c1).
Qed.

Lemma ord_induction_p21d  x y: OIax1b u w0 g ->
   u <=o x -> \2o <=o  y -> x <o (f x y).
Proof.
move=> ax1b ux y2; move: (ax1b) => [ax1 _].
have ox:=proj32 ux.
have lt1:= (ord_induction_p4 fv ax1 ux olt_01).
move: (ole_ltT lt1 (proj33 ax1 _ _ (oleT ux lt1) ux)).
rewrite -(ord_induction_p13 fv ax1b ux OS1) => h1; apply: (olt_leT h1).
move: (proj32_1 h1);rewrite osucc_one => h2. 
case: (equal_or_not \2o y) => yn2; first by rewrite -yn2; fprops.
exact (proj1 (ord_induction_p8 fv ax1 ux (conj y2 yn2))).
Qed.

Lemma ord_induction_p21a x y: OIax1b u w0 g ->
   u <=o x ->  y <o omega0 ->
   (g (w0 x) x) +o y  <=o (f x (osucc y)).
Proof.
move => ax22 ux; move /olt_omegaP; move: (ax22) => [ax1 ax2].
have ox:= proj32 ux.
have ow:= (proj32 (proj32 ax1 _ ux)).
move: y; apply: Nat_induction.
  rewrite osucc_zero osum0r //; rewrite fv ord_induction_y1; fprops.
move=> n nN hrec.
rewrite (succ_of_nat nN).
have on: ordinalp n by apply: OS_cardinal; fprops.
move: (olt0S on) => le1.
rewrite (ord_induction_p13 fv ax22 ux (proj32_1 le1)).
move: (proj33 ax1 _ _ (ord_induction_p41 fv ax1 ux le1) ux) => le2.
rewrite - osum2_succ //; apply /oleSltP; exact: (ole_ltT hrec le2).
Qed.

Lemma ord_induction_p21b x: OIax1b u w0 g ->
  u <=o x -> x +o omega0  <=o (f x omega0).
Proof.
move=> ax ux; move: (ax) => [ax1 ax2].
have ox:= proj32 ux.
have ol:=omega_limit.
rewrite (proj2 (ord_induction_p10 fv ax1 ux) _ ol)(proj2 (osum_normal ox) _ ol).
have ot: ordinal_set(fun_image omega0 (f x)).
  by apply:Os_funI => w /(OS_nat) ;apply: (ord_induction_p5 fv ax1).
apply: ord_ub_sup.
- by apply:OS_sup.
- move => t /funI_P [w wi ->]. 
  move: (proj33 ol _ wi) => so.
  move/(oltP OS_omega):wi =>h; move: (ord_induction_p21a ax ux h) => l1.
  apply:(oleT (oleT (osum_Mleeq (proj32 ax1 _ ux) (proj31_1 h)) l1)).
  apply: ord_sup_ub => //; apply /funI_P; ex_tac.
Qed.


Lemma ord_induction_p21c x y: OIax1b u w0 g ->
  u <=o x -> omega0 <=o y -> x +o y  <=o (f x y).
Proof.
move=> ax ux oy0; move: (ax) => [ax1 ax2].
have loo:=olt_0omega.
have oy1:= proj32 oy0.
have ox:= proj32 ux. move: y oy1 oy0; apply: least_ordinal2 => z oz plz loz.
case: (ole_eqVlt loz) => h1.
  by rewrite - h1; apply:ord_induction_p21b.
case: (ordinal_limA oz) => H. 
   by move: (olt_0omega); rewrite - H => /(oleNgt loz).
  move:H=> [t ot tv]; rewrite tv.
  have lezo: omega0 <=o t by apply /oltSleP; rewrite - tv.
  have lttz : t <o z by rewrite tv; apply: oltS.
  have tp:= (olt_leT loo lezo).
  rewrite - osum2_succ //; apply /oleSltP.
  rewrite (ord_induction_p13 fv ax ux ot). 
  move: (proj33 ax1 _ _ (ord_induction_p41 fv ax1 ux  tp) ux).
  exact:ole_ltT  (plz _ lttz lezo).
rewrite (proj2 (osum_normal ox) _ H).
set T1 := fun_image _ _.
have ot1: ordinal_set T1.
  apply:Os_funI =>  w wi; exact : (OS_sum2 ox (Os_ordinal oz wi)).
have le1:= (olt_leT loo loz).
move: (ord_induction_p5 fv ax1 ux (proj31 H)) => ofo.
apply: (ord_ub_sup ofo) => i /funI_P [j jz ->].
have oj:= Os_ordinal oz jz.
have fi:forall t,  t <o z -> f x t <=o f x z.
  move => t tz; exact (proj1 (ord_induction_p8 fv ax1 ux tz)).
case: (oleT_el OS_omega oj) => cpjo.
  have jy: j <o z by apply /oltP.
  by move: (plz _ jy cpjo) => h; apply: (oleT h); apply: fi.
apply: (oleT (osum_Meqle (proj1 cpjo) ox)).
by apply:  (oleT (ord_induction_p21b ax ux)); apply: fi.
Qed.

Definition critical_ordinal y :=
  [/\ omega0 <=o y, u <o y &
   forall x, u <=o x -> x <o y  -> f x y = y].

Lemma critical_limit y: OIax1b u w0 g -> critical_ordinal y -> limit_ordinal y.
Proof.
move=> ax [pa  pc pd]; move: (ax) => [ax1 ax2].
have oy := proj32 pa.
case: (ordinal_limA oy) => // h; first by move: pc; rewrite h => /olt0.
move:h=> [z oz yv].
move: pc; rewrite yv ; move /oltSleP => le1.
move:(oltS oz); rewrite - yv => lt1.
move: (pd _ le1 lt1).
rewrite yv (ord_induction_p13 fv ax le1 oz) => eq1.
have le3: \2o <=o z.
  apply  /oltSleP; rewrite - yv; exact:(olt_leT olt_2omega pa).
have le2':=(olt_leT olt_02 le3).
move: ((proj33 ax1) _ _ (ord_induction_p41 fv ax1 le1 le2') le1); rewrite eq1.
move /oltSleP => l5.
case: (oleNgt l5 (ord_induction_p21d ax le1 le3)).
Qed.

Lemma is_critical_pr y: OIax1b u w0 g ->
  omega0 <=o y -> u <o y ->
  (forall x, u <=o x ->  x <o y -> f x y <=o y) ->
  critical_ordinal y.
Proof.
move=> ax p1 p2 p3; split => // x ux xy; apply: (oleA (p3 _  ux xy)).
have oy:= proj32 p1.
exact:(oleT (osum_M0le (proj32 ux) oy) (ord_induction_p21c ax ux p1)).
Qed.

Lemma sup_critical A y:  OIax2 u w0 g ->
   omega0 <=o y -> ordinal_set A -> \osup A = y -> 
   (forall x, inc x A -> u <=o x) -> 
   (forall x, inc x A -> f x y = y) -> 
   critical_ordinal y.
Proof.
move=> ax2 ify osA sA uA hA.
move: (ax2) =>[ax1 ax0 _ _]; move: (conj ax1 ax0) => ax.
move: (OS_sup osA); rewrite sA => oy.
case: (emptyset_dichot A) => nea.
  case: (oleNgt ify).
  move: sA; rewrite nea setU_0 -[emptyset]/ \0o => <-; exact: olt_0omega.
have ly2: \2o <=o y. 
  move:  olt_1omega => /oleSltP; rewrite osucc_one => h; exact:(oleT h ify).
have ly1:=(oleT (proj1 olt_12) ly2).
have xp1: forall x, inc x A -> x <o y.
  move => x xA; by move:(ord_induction_p21d ax (uA _ xA) ly2);rewrite (hA _ xA).
have uy: u <o y. 
  move:nea => [x xA]; exact: (ole_ltT (uA _ xA)(xp1 _ xA)).
apply: is_critical_pr => // x ux xy.
have ox:=proj32 ux.
rewrite - sA in xy;move: (olt_sup osA xy)=>  [z zA [zl _]].
by move: (ord_induction_p16 ax2 ux zl (oleR oy)); rewrite (hA _ zA).
Qed.

Lemma sup_critical2 v: OIax2 u w0 g -> ordinalp u -> u +o \2o <=o v ->
  let A:= target (induction_defined0 (fun _ z => f z z) v) in 
  critical_ordinal (\osup A) /\ v <=o (\osup A).
Proof. 
move => ax; move: (ax) => [ax1 ax0 _ _]; move: (conj ax1 ax0) => ax1b.
move: (induction_defined_pr0 (fun _ z => f z z) v) => /=.
set h:= induction_defined0 _ _; move=> [sh sjh h0 hrec] ou lu2v.
have ov:= (proj32 lu2v).
have l2v: \2o <=o v by apply:(oleT (osum_M0le ou OS2) lu2v).
have luv: u <=o v by apply:(oleT (osum_Mle0 ou OS2) lu2v).
have pa: forall n, natp n ->
   [/\ ordinalp (Vf h n), u <=o (Vf h n), v <=o (Vf h n),
   Vf h n <o Vf h (csucc n) & n <o Vf h n].
  apply: Nat_induction.
    have pa:=(olt_leT olt_02 l2v); have pb := (oleR  ov).
    rewrite h0 //; split => //; rewrite (hrec _ NS0) h0.
    apply: ord_induction_p21d => //.
  move=> n nN [pa pb pc pd p]; rewrite (hrec _ nN).
  have pf:= (ord_induction_p21d ax1b pb (oleT l2v pc)).
  have  [pf1 _] := pf.
  have aux:= oleT l2v pc.
  move: (proj32_1 pf)  (oleT pb pf1) (oleT pc pf1)(oleT aux pf1) => a2 a3 a4 a5.
  split => //.
    by rewrite (hrec _ (NS_succ nN))(hrec _ nN); apply: ord_induction_p21d.
  by apply: ole_ltT pf; rewrite (succ_of_nat nN); apply /oleSltP.
have pb: ordinal_set (target h). 
   move=> t tt; move: ((proj2 sjh) _  tt); rewrite sh; move=> [x xs ->].
   by move: (pa _ xs) => [ok _].
move: (OS_sup pb) => os.
set y := union (target h).
move: (sjh) => [fcth _].
have zt: inc v (target h) by rewrite -h0; Wtac => //;rewrite sh; apply: NS0.
have net: nonempty (target h) by ex_tac.
move: (ord_sup_ub pb zt); rewrite -/y => aux1.
split; last by exact.
have pc: u <o y.
  apply:(olt_leT _ (oleT lu2v aux1)).
  by move: (osum_Meqlt olt_02 ou); rewrite (osum0r ou) => le1.
case: (ord_sup_inVlimit pb net) => yt.
  move: ((proj2 sjh) _ yt) => [v' vsh vv].
  rewrite sh in vsh; move: (pa _ vsh) => [_ _ _ aux _]. 
  rewrite -vv in aux.
  have pd:inc (Vf h (csucc v')) (target h ) by Wtac; rewrite sh; apply:NS_succ.
  case: (oltNge aux (ord_sup_ub pb pd)).
apply: is_critical_pr => //.
  split => //; fprops; move => t tN; apply /(oltP os).
  move: (pa _ tN)=> [_ _ _ _ lt1]; apply: (olt_leT lt1).
  apply ord_sup_ub => //; Wtac; rewrite sh; fprops.
move => x ux xy.
move: (proj32_1 pc) => oy.
move: (ord_induction_p10 fv (proj1 ax1b) ux) => [_ nf5]. 
rewrite (nf5 _ yt) -/y; apply: ord_ub_sup => //.
move=> i /funI_P [j /(oltP oy) jy ->].
have fi: forall n, natp n -> 
   forall m, natp m -> Vf h m <=o Vf h (m +c n).
  apply: Nat_induction.
     move=> m mN; rewrite (Nsum0r mN); apply: oleR.
     apply: pb; Wtac; ue.
  move=> n nN hr m mN; apply: (oleT (hr _ mN)).
  by rewrite (csum_nS _ nN);move: (pa _ (NS_sum mN nN))=> [_ _ _ [hh _] _].
move: (olt_sup pb xy) => [n nt [un _]]. 
move: (olt_sup pb jy) => [m mt [um _]]. 
move: ((proj2 sjh) _  nt)((proj2 sjh) _  mt)=> [N Nv u1] [M Mv u2].
rewrite sh in Nv Mv; move: (fi _ Nv _ Mv); rewrite -u2. 
move: (fi _ Mv _ Nv); rewrite -u1 csumC=> le1 le2.
have le3:= oleT un le1.
have le4:= oleT um le2.
have ns: natp (M +c N) by apply: NS_sum.
have ns1:= NS_succ ns.
move: (ord_induction_p16 ax ux le3 le4) => pd; apply: (oleT pd).
rewrite - hrec;[ apply: ord_sup_ub;[| Wtac; rewrite sh] |]; fprops.
Qed.

Lemma sup_critical3 A:  OIax2 u w0 g -> nonempty A -> 
   (forall x, inc x A -> critical_ordinal x) -> 
   critical_ordinal (\osup A).
Proof.
move => ax; move: (ax) => [ax1 ax0 _ _]; move: (conj ax1 ax0) => ax1b.
move => neA hA.
have oA: ordinal_set A by  move=> x xA; move: (hA _ xA) =>[ /proj32].
case: (inc_or_not (union A) A) => nuaa; first by apply: hA.
case: (ord_sup_inVlimit  oA neA) => ca; first by apply: hA.
have osA: ordinalp (\osup A) by apply: OS_sup.
move: neA => [t tA];move: (ord_sup_ub oA tA) => lty.
move: (hA _ tA) => [ot  p3 p4].
have ou:=oleT ot lty.
have ou':=(olt_leT p3 lty).
apply: is_critical_pr => // x ux xu.
rewrite (proj2 (ord_induction_p10 fv ax1 ux) _ ca); apply: ord_ub_sup => //.
move => i /funI_P [j ji ->].
have [z [z1 z2 z3]]: exists z, [/\ x <=o z, j <=o z & z <o union A].
  move: (proj32 ux) (Os_ordinal osA ji) => ox oj.
  move: (oleR oj)(oleR ox) => lej lex.
  case: (oleT_ee ox oj) => le.
    by exists j; split => //; apply/(oltP osA).
    by exists x.
move /(oltP osA): (z3) => z4.
move: ca => [_ _ h]; move: (h z z4);  move /(oltP osA) => h1.
move: (olt_sup oA h1) => [v vA zv].
have lt1:=(oltS (proj32 z1)).
have lt2:= (olt_ltT lt1 zv).
have le4:= (oleT z2 (proj1 lt2)).
have le3:= oleT ux z1.
apply: (oleT (ord_induction_p16 ax ux z1 le4)).
by move:(hA _ vA)=> [_ _  H]; rewrite (H _ le3 lt2); apply: ord_sup_ub.
Qed.

Lemma critical_closed_proper: OIax2 u w0 g ->  ordinalp u ->
  iclosed_proper critical_ordinal.
Proof.
move => ax2 ou.
split.
  split;first by move => t [/proj32].
  by move => F HF neF; apply:sup_critical3.
apply: unbounded_non_coll => x ox.
have ou2 := OS_sum2 ou OS2.
set t := x +o (u +o \2o).
case:(sup_critical2 ax2 ou (osum_M0le ox ou2)); set y := \osup _ => qa qb.
exists y => //; exact: (oleT (osum_Mle0 ox ou2) qb).
Qed.
  
Lemma critical_indecomposable y: OIax2 u w0 g ->
  critical_ordinal y -> indecomposable y.
Proof.
move => ax; move: (ax) => [ax1 ax0 _ _]; move: (conj ax1 ax0) => ax1b.
move=> [y1 y3 y4].
have oy := proj32 y1.
have yp:= (ole_ltT (ole0x (proj31_1 y3)) y3).
apply/(indecompP yp) => x xy.
move: (proj31_1 xy)  (proj31_1 y3) => ox ou.
apply: oleA; last exact: (osum_M0le ox oy).
have pa: forall t, u <=o t -> t +o y <=o (f t y). 
  by move => t tp; apply: ord_induction_p21c.
case: (oleT_ee ox ou) => lexu.
  have leuu:= (oleR ou).
  rewrite - {2} (y4 _ leuu y3);  apply: oleT (pa _ leuu).
  by apply: osum_Mleeq.
by rewrite - {2} (y4 _ lexu xy); apply: pa.
Qed.

End OrdinalInduction2.



(** ** Ordinal power *)

Definition opow' := ord_induction_defined (fun z:Set => \1o) oprod2.
Definition opow a b := 
  Yo (a = \0o) 
     (Yo (b = \0o) \1o \0o)
     (Yo (a = \1o) \1o (opow' a b)).
Notation "x ^o y" := (opow x y) (at level 30).

Lemma ord_pow_axioms:  OIax3 \2o (fun z:Set => \1o) oprod2.
Proof.
move: (olt_12) (olt_02) => l12 l02.
split; first split; first split.
-  move => a a2 /=; rewrite (oprod1l (proj32 a2)); exact: (olt_leT l12 a2).
-  move => a [_ a2 _] /=; rewrite (oprod1l a2); exact: (oleR a2).
-  move => a b a2 b2; apply:(oprod_Meq1lt (olt_leT l12 b2) (olt_leT l02 a2)).
-  by move => a b a' b' la lb; apply:oprod_Mlele.
-  move => _ _ _ _ /=;fprops.
-  move => a b [_ oa _] ab /=; rewrite !oprod1l //; exact: (proj32_1 ab).
-  by move => a [_ oa _] /=; rewrite oprod1l.
-  move => a ab; apply: normal_ofs_equiv2; fprops; apply: oprod_normal.
   exact:(olt_leT l02 ab).
-  by move => a b c [_ oa _] [_ ob _][_ oc _]; symmetry;apply:oprodA.
Qed.


Lemma opow00: \0o ^o \0o = \1o.
Proof. by rewrite /opow; Ytac0; Ytac0. Qed.

Lemma opow0x x: x <> \0o ->  \0o ^o x = \0o.
Proof. by move=> xnz; rewrite /opow; Ytac0; Ytac0. Qed.

Lemma opow0x' x: \0o <o x ->  \0o ^o x = \0o.
Proof. by move => [_ /nesym h]; apply:opow0x. Qed.

Lemma opow1x  x: \1o ^o x = \1o.
Proof. 
have ooz: (\1o <> \0o) by fprops.
by rewrite /opow; Ytac0; Ytac0.
Qed.

Lemma opowx0 x: x ^o \0o = \1o.
Proof.  
rewrite /opow /opow'.
Ytac xnz; [by Ytac0 | by Ytac xno => //; rewrite ord_induction_y0 ].
Qed.

Lemma opowx1 x: ordinalp x -> x ^o \1o = x.
Proof.  
have zno: \1o <> \0o by fprops.
rewrite /opow; Ytac xz; [by Ytac0 |Ytac xno => // ].
move => ox;rewrite /opow' ord_induction_y1 oprod1l //. 
Qed.

Lemma opow2x x y: \2o <=o x ->  x ^o y = opow' x y.
Proof.
move=> x2; rewrite /opow.
by move: (ord2_trichotomy1 x2) => [p1 p2]; Ytac0; Ytac0.
Qed.

Lemma OS_pow x y: ordinalp x -> ordinalp y ->
  ordinalp (x ^o y).
Proof.
move=> ox oy.
case: (ord2_trichotomy ox).
- move=> xz; case: (equal_or_not y \0o) => yz.
    rewrite xz yz opow00; fprops.
  rewrite xz opow0x //; fprops.
- by move => xo; rewrite xo opow1x; fprops.
- move:(ord_pow_axioms) =>[ [ax1 _ _ _] _ _ _].
  move => xo; rewrite (opow2x _ xo). 
  apply:(ord_induction_p5 (erefl opow') ax1 xo oy).
Qed.

Global Hint Resolve OS_pow : fprops.

Lemma opow_normal x: \2o <=o x ->
  normal_ofs (opow x).
Proof.
move=> x2; move: ord_pow_axioms => [[ax1 ax2 _ _ ] _ _ _].
move: (ord_induction_p10 (erefl opow') ax1 x2).
have op: forall y, x ^o y = opow' x y by move=> y ; apply: opow2x.
move => [pa pb];split; first by move =>  u v; rewrite /= op op; apply: pa.
by move => a al; rewrite op (pb _ al); apply: ord_sup_2funI => u; rewrite op.
Qed.

Lemma opow_Meqle1 x y: \0o <o x -> \0o <o y  -> x <=o (x ^o y).
Proof.
move=> /oge1P x2 y1.
case: (equal_or_not \1o x) => o1.
  rewrite - o1 opow1x; apply: oleR; fprops.
have o3: \2c <=o x  by apply /oge2P; split.
move: ord_pow_axioms => [ [ax1 _ _ _] _ _ _].
move: (ord_induction_p4 (erefl opow') ax1 o3 y1);rewrite opow2x //.
Qed. 

Lemma opow_Mspec x y: \2o <=o x ->
  ordinalp y  -> y <=o (x ^o y).
Proof.
move=> x2 y1.
move: ord_pow_axioms => [ [ax1 _ _ _] _ _ _].
move: (ord_induction_p9 (erefl opow') ax1 x2 y1); rewrite opow2x //.
Qed. 

Lemma opow_Meqlt x y y': \2o <=o  x ->
  y <o y' -> (x ^o y) <o (x ^o y').
Proof.
move=>  x2 yy'.
move: ord_pow_axioms => [ [ax1 _ _ _] _ _ _].
move: (ord_induction_p8 (erefl opow') ax1 x2 yy'); rewrite !opow2x //.
Qed.

Lemma opow_Meqltr a b c: \2o <=o a ->
  ordinalp b -> ordinalp c -> 
  ((b <o c) <-> ( (a ^o b) <o (a ^o c))).
Proof.
move=> h ob oc.
split; first by apply: opow_Meqlt.
move=> aux; case: (oleT_ell oc ob).  
- by move=> cb; move: aux => [_]; rewrite cb.
- by move=> h1;move: (opow_Meqlt h h1)  => [/(oltNge aux) ].
- done.
Qed.

Lemma opow_regular a b c: \2o <=o a ->
  ordinalp b -> ordinalp c -> a ^o b = a ^o c -> b = c.
Proof.
move=> h ob oc.
case: (oleT_ell ob oc) => //h1; move: (opow_Meqlt h h1) => [_ h2] //.
by move=> h3; case: h2.
Qed.
  
Lemma opow_nz0 x y:
  ordinalp x -> ordinalp y -> x ^o y = \0o ->
  (x = \0o /\ y <> \0o).
Proof.
move=> ox oy pz.
case: (equal_or_not y \0o) => ynz.
  move: pz;  rewrite ynz; rewrite opowx0 => h'. 
  by case: (card1_nz).
split => //.
case: (equal_or_not x \0o) =>// xnz.
have xp:= (ord_ne0_pos ox xnz).
have yp:= (ord_ne0_pos oy ynz).
move: (opow_Meqle1 xp yp); rewrite pz; apply: ole0.
Qed.

Lemma opow_pos a b: \0o <o a -> ordinalp b -> \0o <o (a ^o b).
Proof.
move=> ap ob; move: (ap) => [[_ oa _] anz].
apply: ord_ne0_pos; fprops => bad; case: anz.
by move: (opow_nz0 oa ob bad) => [-> _].
Qed.

Lemma opow2_pos a b: \2o <=o a -> ordinalp b -> \0o <o (a ^o b).
Proof. move /(olt_leT (olt_02)); apply: opow_pos. Qed.

Lemma opow_Mlele x x' y y':
  x <> \0o ->  x <=o x' -> y <=o y' ->
  (x ^o y) <=o (x' ^o y').
Proof.
move=> xnz xx' yy'.
have [ox ox' _] := xx'.
have oy':=(proj32 yy').
case: (ord2_trichotomy ox) => // x2.
   rewrite x2 opow1x; apply: oge1; fprops => h.
   move: (opow_nz0 ox' oy' h) => [p1 p2].
   by rewrite p1 in xx'; move: (ole0 xx'). 
move: ord_pow_axioms => [ax1 _ _ _ ]. 
move: (ord_induction_p16 (erefl opow') ax1 x2 xx' yy'). 
by rewrite - (opow2x _ x2) -  (opow2x _ (oleT x2 xx')).
Qed.

Lemma opow_Mleeq x x' y:
  x <> \0o ->  x <=o x' -> ordinalp y ->
  (x ^o y) <=o (x' ^o y).
Proof. by move => xne le1 /oleR oy; apply:opow_Mlele. Qed.

Lemma opow_Meqle x y y':
  \0o <o x -> y <=o y' ->  (x ^o y) <=o (x ^o y').
Proof. 
move => [[_ ox _] xn] le1 ; apply: opow_Mlele;fprops.
Qed.

Lemma opow_eq_one x y : ordinalp x -> ordinalp y -> x ^o  y = \1o ->
    (x = \1o \/ y = \0o).
Proof.
move => ox oy p1.
case: (ozero_dichot oy) => yp; [ by right | left].
case: (ozero_dichot ox) => xp; first by move: p1; rewrite xp opow0x'.
move:(opow_Meqle1 xp yp); rewrite p1 => h.
by move /oge1P: xp; apply:oleA.
Qed.

Lemma opow_sum a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  a ^o (b +o c) = (a ^o b) *o  (a ^o c).
Proof.
move=> oa ob oc.
case: (ozero_dichot ob) => bz.
  rewrite bz opowx0 (osum0l oc) (oprod1l) => //; fprops.
case: (ozero_dichot oc) => cz.
  rewrite cz opowx0 (osum0r ob) (oprod1r) => //; fprops.
case: (ord2_trichotomy oa) => az.
- rewrite az (opow0x' bz) (opow0x' cz) opow0x.
    rewrite oprod0r => //; fprops.
  by move=> sz; move: (osum_Mle0 ob oc); rewrite sz => /(oltNge bz).
- rewrite az (opow1x b) (opow1x c)(opow1x (b +o c)).
  rewrite oprod1r //; fprops.
- move: (ord_induction_p18 (erefl opow') ord_pow_axioms az bz cz).
  rewrite (opow2x b az)(opow2x c az) (opow2x (b +o c) az) //.
Qed.

Lemma opow_succ x y: ordinalp x -> ordinalp y ->
  x ^o (osucc y) = (x ^o y) *o x.
Proof.
by move=> ox oy;rewrite -(osucc_pr oy) (opow_sum ox oy OS1) opowx1.  
Qed.


Lemma opow_prod: forall a b c,
  ordinalp a -> ordinalp b -> ordinalp c ->
  a ^o (b *o c) = (a ^o b) ^o c.
Proof.
move=> a b c oa ob oc.
case: (equal_or_not b \0o) => bz.
  by rewrite bz (oprod0l)  (opowx0 a)  (opow1x c).
case: (equal_or_not c \0o) => cz.
  by rewrite cz  (oprod0r) !opowx0.
have b1:= (ord_ne0_pos ob bz).
have c1:= (ord_ne0_pos oc cz).
case: (ord2_trichotomy oa) => az.
    rewrite az (opow0x bz) (opow0x cz) opow0x //.
    by apply: oprod2_nz.
  rewrite az (opow1x b) (opow1x c)(opow1x (b *o c)) //.
move: (ord_induction_p19 (erefl opow') ord_pow_axioms az b1 c1).
rewrite (opow2x b az)(opow2x (b *o c) az). 
suff: (\2o <=o (opow' a b)) by  move => f2; rewrite (opow2x c f2) //.
apply: (ord_induction_p41 (erefl opow') _ az b1).
by move: ord_pow_axioms  => [[]].
Qed.


Lemma opow_2int a b: natp a ->natp b -> a ^o b = a ^c b.
Proof.
move=> aN bN;move: b bN.
move: (OS_nat aN) => oa.
apply: Nat_induction; first by rewrite cpowx0 opowx0.
move=> n nN hrec.
rewrite (cpow_succ _ nN)  (succ_of_nat nN) (opow_succ oa (OS_nat nN)) hrec.  
apply: (oprod2_2int); fprops.
Qed.

Lemma opow_2int1 a b: a <o omega0 -> b <o omega0 -> (a ^o b) <o omega0.
Proof.
move /olt_omegaP => aN /olt_omegaP bN; apply /olt_omegaP.
rewrite (opow_2int aN bN); fprops.
Qed.

Lemma cnext_pow C x y: 
  infinite_c C -> inc x (cnext C) -> inc y (cnext C) ->
  inc (x ^o y) (cnext C).
Proof.
move => ha hx; move: (ha) => [cc _].
move /(cnextP cc): (hx) => [ox cx] /(cnextP cc) [oy cy].
have s1: inc \1o (cnext C). 
  by apply:cnext_leomega => //; move: olt_1omega => [].
case: (ord2_trichotomy ox).
    case: (equal_or_not y \0o); first by move => ->; rewrite opowx0.
    move => ynz ->; rewrite opow0x //.
    apply:(cnext_leomega ha (proj1 olt_0omega)).
  by move => ->; rewrite opow1x.
move => x2;move: y oy cy; apply:least_ordinal2 => z oz hz coz.
have aux: forall t, t<o z -> inc (x ^o t) (cnext C).
  move => t sa; apply: (hz _ sa). 
  exact: (cleT  (ocle1 (proj1 sa)) coz).
case: (ordinal_limA oz); first by move => ->; rewrite opowx0.
  move=> [t ot zt].
  have tz: t <o z by rewrite (oltP oz) zt /osucc; fprops.
  move: (aux _ tz) =>  ee.
  by rewrite zt (opow_succ ox ot); apply: cnext_prod.
move => lz.
rewrite (proj2 (opow_normal x2) _ lz); apply: cnext_sup => //.
   apply: cleT coz; apply: fun_image_smaller.
by move => j /funI_P [k /(oltP oz) kz ->];apply: aux.
Qed.

Lemma opow_countable x y:
   countable_ordinal x -> countable_ordinal y -> countable_ordinal (x ^o y).
Proof.
move: CIS_omega aleph_oneP => h T.
by move => /T xa /T xn; apply /T;apply:cnext_pow.
Qed.

Lemma opow_Mspec2 a b: ordinalp b ->
  \2o <=o a -> (a *o b) <=o (a ^o b).
Proof.
move=> ob oa2.
have oa:= proj32 oa2. 
have a1:=(olt_leT olt_02 oa2).
move: (ord2_trichotomy1 oa2) => [pa1 pa2].
move: b ob;apply: least_ordinal2 => t ot lpy.
case: (ordinal_limA ot).  
    move => ->;rewrite opowx0 oprod0r; exact: ole_01.
  move=> [y oy ty].
  rewrite ty (opow_succ oa oy) (oprod2_succ oa oy).
  case: (ozero_dichot oy) => ynz.
    rewrite ynz oprod0r opowx0 osum0l // oprod1l;fprops.
  have op:= (OS_pow oa oy).
  move: (oprod_Mlele (oleR op)  oa2).
  rewrite (ord_double op)=> le1.
  have lpyc: y <o t by rewrite ty; apply: oltS.
  move: (lpy _ lpyc)=> le2.
  have au: a <=o (a ^o y) by apply: opow_Meqle1.
  exact:(oleT (osum_Mlele le2 au) le1).
move=> tl.
rewrite (proj2 (oprod_normal a1) _ tl).
have pato:= (OS_pow oa ot).
apply: ord_ub_sup  => //.
move=> i /funI_P [z /(oltP ot) zt ->].
apply: (oleT (lpy _ zt));exact:(opow_Meqle a1 (proj1 zt)).
Qed.


Definition oopow x := omega0 ^o x.

Lemma oopow_pos x: ordinalp x -> \0o <o oopow x.
Proof. move => ox; apply: opow2_pos => //; apply: ole_2omega. Qed.

Lemma oopow_nz x: ordinalp x -> oopow x <> \0o.
Proof. by move=> /oopow_pos [_ /nesym]. Qed.

Lemma opow_Mo_le a b: a <=o b -> (oopow a) <=o (oopow b).
Proof. move=> lab; apply:  (opow_Meqle olt_0omega lab). Qed.

Lemma opow_Mo_lt a b:  a <o b -> (oopow a) <o (oopow b).
Proof.
move=> ab; apply: opow_Meqlt => //; apply: ole_2omega.
Qed.

Lemma opow_Mo_leP a b: ordinalp a -> ordinalp b ->
  (a <=o b <-> (oopow a) <=o (oopow b)).
Proof.
move=> oa ob; split; first apply:opow_Mo_le.
move => loo.
by case: (oleT_el oa ob) => //; move/(opow_Mo_lt) => /oltNge. 
Qed.

Lemma opow_Mo_ltP a b: ordinalp a -> ordinalp b ->
   (a <o b <-> (oopow a) <o (oopow b)).
Proof. move=> oa ob; exact: (opow_Meqltr ole_2omega oa ob). Qed.

Lemma oopow_succ x: ordinalp x -> oopow (osucc x) = oopow x *o omega0.
Proof. by move => ox; rewrite /oopow (opow_succ OS_omega ox). Qed.

Lemma OS_oopow x: ordinalp x ->  ordinalp (oopow x).
Proof. move => ox; exact: (OS_pow OS_omega ox). Qed.

Lemma oopow0: oopow \0o = \1o.
Proof. apply:opowx0. Qed.

Lemma oopow1: oopow \1o = omega0.
Proof. apply:(opowx1 OS_omega). Qed.

Lemma omega_log_p1 x: \0o <o x -> 
   exists y, [/\ ordinalp y, oopow y <=o x & x <o oopow (osucc y)]. 
Proof.
move => ox.
have x1: \1o <=o x by apply/oge1P.
have o2:= ole_2omega.
move: ord_pow_axioms => [[ax1 _ _ _ ] _ _ _].
move: (ord_induction_p12 (erefl opow') ax1 o2 x1) => [y []].
rewrite - (opow2x _ o2) -(opow2x _ o2) => sa sb sc.
by have oy:=(proj31 sa); exists y. 
Qed.

Definition ord_ext_div_pr a b x y z :=
  [/\ ordinalp x, ordinalp y, ordinalp z &
  [/\ b =  ((a ^o x) *o y) +o z,
   z <o (a ^o x), y <o a & \0o <o y]].

Lemma ord_ext_div_unique a b x y z x' y' z':
  \2o <=o a -> ordinalp b -> 
  ord_ext_div_pr a b x y z ->  ord_ext_div_pr a b x' y' z' ->
  [/\ x=x', y=y' & z=z'].
Proof.
move=> pa ob.
have oa:= proj32 pa.
have aux: forall x y z, ord_ext_div_pr a b x y z -> 
  (a ^o x <=o b /\ b <o a ^o (osucc x)).
  move => u v w [ou ov ow [-> r1 r2 r3]]; move: (OS_pow oa ou) => op; split.
    apply:(oleT (oprod_Mle1 op r3)); apply:(osum_Mle0 (OS_prod2 op ov) ow).
  apply:(olt_leT (osum_Meqlt r1 (OS_prod2 op ov))).
  rewrite - (oprod2_succ op ov) (opow_succ oa ou); apply:oprod_Meqle => //. 
  by apply /oleSltP.
move => p1 p2.
move: (aux _ _ _ p1) (aux _ _ _ p2) => [p3 p4][p5 p6].
move: p1 p2 => [ox oy oz [bv r1 r2 r3]][ox' oy' oz' [bv' r1' r2' r3']].
have sx: x = x'.
   move: (proj1 (opow_normal pa)) => h.
   apply: (sincr_bounded_unique h ox ox' p3 p4 p5 p6). 
rewrite - sx in  bv' r1'.
have p7 : (odiv_pr0 b (a^o x) y z) by split.
have p8 : (odiv_pr0 b (a^o x) y' z') by split.
by move: (odivision_unique ob (OS_pow oa ox) p7 p8) => [e1 e2].
Qed.


Lemma ord_ext_div_exists a b:
  \2o <=o a -> \0o <o b -> 
  exists x y z,  ord_ext_div_pr a b x y z.
Proof.
move=> a2 b1.
move: (proj32 a2) (proj32_1 b1) => oa ob.
case: (oleT_el oa ob); last first.
  move=> ba; exists \0o; exists b; exists \0o; hnf. 
  rewrite (opowx0 a) (oprod1l ob)(osum0r ob).
  move: OS0 => o0; split => //; split => //;by apply olt_01.
move=> ab.
have b11: \1o <=o b by apply/oge1P.
move: ord_pow_axioms => [[ax1 _ _ _ ] _ _ _].
move: (ord_induction_p12 (erefl opow') ax1 a2 b11) => [y].
rewrite -(opow2x y a2) -(opow2x (osucc y) a2).
move=> [yb fyb fysb].
have oy:=proj31 yb.
move: fysb; rewrite (opow_succ oa oy). 
move:(OS_pow oa oy)=> oay ltb. 
move: (odivision_exists oay oa ltb)=> [[oq or abq lt1] lt2].
exists y, (oquo b (a ^o y)), (orem b (a ^o y)); split => //; split => //.
apply/ord_ne0_pos => // qz; move: abq; rewrite qz (oprod0r) (osum0l or) => h.
by apply/(oltNge lt1); rewrite -h.
Qed.

Lemma opow_rec_def a b: \2o <=o a -> ordinalp b ->
  a ^o b = unionb (Lg b (fun x => 
    fun_image( (a-s1 \0o)\times a ^o x) (fun p => (a^o x) *o (P p) +o (Q p))))
    +s1 \0o.
Proof.
move => a2 ob.
have oa:= proj32 a2. 
have ap:= (olt_leT olt_02 a2).
have oab:= OS_pow oa ob.
set_extens t => h; last first.
  apply /(oltP oab);case /setU1_P:h; last first.
    by move => ->; apply: opow_pos.
  move => /setUb_P; aw; move => [x xa]; rewrite LgV//.
  move/(oltP ob): xa => lxb.
  have ox:= (proj31_1 lxb).
  have oax:=  (OS_pow oa ox).
  move /funI_P => [p /setX_P [pp /setC1_P [ua unz] /(oltP oax) vb] ->].
  have ou:= (Os_ordinal oa ua).
  move:ua => /(oltP oa) /oleSltP ua.
  move:(osum_Meqlt vb (OS_prod2 oax ou)) => h; apply: (olt_leT h).
  rewrite - (oprod2_succ oax ou).
  move:(oprod_Meqle ua oax); rewrite - (opow_succ oa ox).
  move => h1; apply: (oleT h1); apply: opow_Meqle => //.
  by apply/oleSltP.
have ot:= (Os_ordinal oab h).
apply/setU1_P;case:(ozero_dichot ot);[ by right | move => tnz ; left].
move: (ord_ext_div_exists a2 tnz) => [x [y [z [ox oy oz [tv r1 r2 r3]]]]].
have aux: inc x b.
  apply /(oltP ob); case: (oleT_el ob ox) => // bx.
  move: (oleT (opow_Meqle ap bx) (oprod_Mle1 (proj32_1 r1) r3))=> l1.
  move: (oleT l1 (osum_Mle0 (proj32 l1) oz)); rewrite - tv => l2.
  by move /(oltP oab):h => /(oleNgt l2).
apply/setUb_P; aw; exists x => //; rewrite LgV//.
apply /funI_P; exists (J y z); aw; trivial;apply: setXp_i => //.
   apply /setC1_P; split; [ by apply/(oltP oa) | exact: nesym (proj2 r3)].
exact: (olt_i r1).
Qed.


Lemma indecomp_prop3 x: 
  indecomposable x -> exists2 y, ordinalp y & x = oopow y.
Proof.
move=> oidx.
move:(ord_ext_div_exists (ole_2omega) (proj1 oidx)) => [a [b [c]]].
move => [oa ob oc [pa pb pc pd]].
symmetry in pa.
have op:= proj32_1 pb.
move: (olt_leT pb (oprod_Mle1 op pd)) => lt1.
have op1:= (proj32_1 lt1).
case: (indecomp_pr op1 oc oidx pa) => eq1; last first.
  by move: (proj2 (olt_leT lt1 (osum_Mle0 op1 oc))); rewrite pa eq1.
  have bN: natp b by exact (olt_i pc).
have bz:= nesym (proj2 pd).
move: (cpred_pr bN bz)=> []; set b1:= cpred b. 
move => ra;rewrite (succ_of_nat ra) => rb.
move:(OS_nat ra) => ob1;move: (OS_prod2 op ob1) => h2.
move: eq1; rewrite rb (oprod2_succ op ob1) => h1.
case:(indecomp_pr (OS_prod2 op ob1) op oidx h1) => eq2.
  by case: (oopow_nz oa);move:(osum2_a_ab h2 op); rewrite h1;apply.
by exists a.
Qed.

Lemma indecomp_prop4 y: ordinalp y ->
  indecomposable (oopow y).
Proof.
move: y;apply: least_ordinal2 => z oz zle.
case:(ordinal_limA oz)=> zl.
    rewrite zl oopow0; exact indecomp_one.
  move: zl => [x ox zv]. 
  rewrite zv (oopow_succ ox). 
  apply/(indecomp_prodP olt_1omega (oopow_pos ox));apply: indecomp_omega.
rewrite /oopow (proj2 (opow_normal (ole_2omega)) _ zl).
set E := (fun_image z oopow).
have pa: (forall x, inc x E -> indecomposable x). 
  by move => x /funI_P [t /(oltP oz) tz ->]; apply: zle.
apply:(indecomp_sup pa); exists \1o; apply/funI_P. 
by exists \0o; [exact (proj32 zl) | rewrite oopow0 ].
Qed.

Lemma indecomp_limit2 n: \0o <o n ->  limit_ordinal (oopow n).
Proof.
move => [[_ on _] nz].
case: (indecomp_limit (indecomp_prop4 on)) => // pa.
case:(opow_eq_one OS_omega on pa) => h; first by case: (proj2 olt_1omega).
by case: nz.
Qed.

Lemma indecomp_enum:
  oopow =1o ordinalsf indecomposable.
Proof.
set p := indecomposable.
have opp: ordinal_prop p by move => x [/proj32_1 h _].
have p4 :(iclosed_collection p) by split => // F fl nef; apply: indecomp_sup.
move:ole_2omega  OS_omega => oo odo.
have p5: (non_coll p). 
   apply:unbounded_non_coll => // x ox; exists(omega0 ^o x). 
     apply: (opow_Mspec oo ox).
   by apply: indecomp_prop4.
apply:(normal_ofs_uniqueness (p:= fun z => z *o omega0)). 
- apply: (opow_normal oo).
- by apply: (ordinals_col_p2 (conj p4 p5)).
- by move => x ox; rewrite oopow_succ.
- move => x /(iclosed_col_fs (conj p4 p5)).
  set u := ordinalsf p x; set v := ordinalsf p (osucc x).
  move => [uv pu pv h]; move: uv h; move/indecomp_prop3:pu => [a oa ->].
  move/indecomp_prop3:pv => [b ob ->] /(opow_Meqltr oo oa ob) => lab h.
  rewrite - (opow_succ odo oa); ex_middle bad.
  have ra := (opow_Meqlt oo (oltS oa)).
  have rb := (indecomp_prop4 (OS_succ oa)).
  move /(opow_Meqltr oo ob (OS_succ oa)):(conj (h _ rb ra) bad).
  by move /oltSleP => /(oltNge lab).
- move: (iclosed_col_f0 (conj p4 p5)); set u := ordinalsf p \0o.
  rewrite oopow0; move => [[/oge1P up _] h].
  apply:oleA => //; exact: (h _ indecomp_one).
Qed.

Lemma oprod_fix1 a y (x := a ^o omega0 *o y):  
  \0o <o a  -> ordinalp y -> a *o x = x.
Proof.
move => ap oy. 
have oa:= proj32_1 ap.
rewrite (oprodA oa (OS_pow oa OS_omega) oy)  -{1} (opowx1 oa).
by rewrite - (opow_sum oa OS1 OS_omega) (osum_int_omega olt_1omega).
Qed.

Lemma oprod_fix2 a x: \0o <o a -> ordinalp x -> a *o x = x ->
  exists2 y, ordinalp y & x =  a ^o omega0 *o y.
Proof.
move => ap ox xp.
case: (oquoremP ox (opow_pos ap OS_omega)).
set q:= (oquo _ _); set r := orem _ _;move=> oq or xv rs.
have oa:= proj32_1 ap.
have ofp:=(OS_prod2 (proj32_1 rs) oq).
move: (oprodD ofp or oa); rewrite -xv xp xv (oprod_fix1 ap oq) => eq1.
move:( osum2_simpl or (OS_prod2 oa or) ofp eq1) => rar.
have ran: forall n, inc n Nat -> r = a ^o n *o r. 
  apply: Nat_induction; first by rewrite opowx0 oprod1l.
  move => n nN h; move:(OS_nat nN) => os.
  have ->: csucc n = \1o +o n.
    by rewrite (osum2_2int NS1 nN) csumC Nsucc_rw.
  by rewrite (opow_sum oa OS1 os)(opowx1 oa) -(oprodA oa (OS_pow oa os) or) -h.
case:(equal_or_not r \0o) => rz;  first by exists q => //; rewrite rz osum0r.
case: (oone_dichot ap) => a2.
  by move: rs rz; rewrite a2 opow1x; move /olt1.
case:(oltNge  rs).
move/oge2P : a2 => a2; rewrite(proj2 (opow_normal a2) _ omega_limit).
apply: ord_ub_sup => //.
move => w /funI_P [n nN ->].
rewrite (ran _ nN); move:(OS_nat nN) => os. 
by apply:oprod_Mle1; [ fprops | apply/ord_ne0_pos ].
Qed.


Lemma mult_fix_enumeration a: \0o <o a ->
  first_derivation (oprod2 a) =1o (oprod2 (a ^o omega0)).
Proof.
move => ap.
set b := a ^o omega0.
have oa:= proj32_1 ap.
have ob: ordinalp b by apply: (OS_pow oa OS_omega).
have bp: \0o <o b by apply: opow_pos => //; apply: OS_omega.
move: (oprod_normal ap) (oprod_normal bp) => npa npb.
move: (iclosed_fixpoints npa) => pa.
move:(ordinals_col_p2 pa) => na.
have w0: first_derivation (oprod2 a) \0o = b *o \0o.
  rewrite oprod0r.
  have h: ordinalp \0o /\ a *o \0o = \0o by split; [ fprops| apply: oprod0r].
  by move: (iclosed_col_f0 pa) => [_ sc]; move: (sc _ h) => /ole0.
apply:(normal_ofs_uniqueness (p:= fun z => z+o b)) => //; last first.
  by move => x ox; apply: oprod2_succ.
move => x ox.
move: (iclosed_col_fs pa ox); rewrite /first_derivation.
set u:= ordinalsf _ x; set v := ordinalsf _ (osucc x).
move => [sa [ou sb] [ov sc] sd].
move: (oprod_fix2 ap ou sb) => [y oy uv].
move: (oprod_fix2 ap ov sc) => [z oz vv].
move: (OS_succ oy) => osu.
move: (conj (OS_prod2 ob osu) (oprod_fix1 ap osu)) => ea.
move:(oprod_Meqlt (oltS oy) bp); rewrite - uv => eb.
move: (sd _ ea eb); rewrite uv - (oprod2_succ ob oy) vv -/b => h1.
ex_middle h2.
rewrite  uv vv in sa;move: (oprod_Meqltr oy oz ob sa) => /oleSltP l1.
case: (oleNgt l1 (oprod_Meqltr oz osu ob (conj h1 h2))).
Qed.


(** repeated derivations *)

Lemma closed_cofinal_inter C S (E := cnext C) (T:= intersectionb S):
  infinite_c C -> fgraph S -> ordinalp (domain S) -> 
  cardinal (domain S) <=c C ->
  nonempty (domain S) ->
  (forall i, inc i (domain S) -> iclosed_set (Vg S i)) ->
  (forall i, inc i (domain S) -> ord_cofinal (Vg S i) E) ->
  (forall i j, i<o j -> inc i (domain S) -> inc j (domain S) ->
       sub (Vg S j) (Vg  S i)) ->
  iclosed_set T /\ ord_cofinal T E.
Proof.
move => ic fgs ods cds /nonemptyP neds h1 h2 h4.
move: (cnext_pr1 (proj1 ic)) => [sa sb sc].
have pa:=(olt_i (ord_ne0_pos ods neds)). 
have h3:  (forall i, inc i (domain S) -> sub (Vg S i) E) by move => i /h2 [].
have pb: sub T E by move => x h; move:(setIb_hi h pa); apply: h3.
move: (infinite_card_limit2 (cle_inf_inf ic (proj1 sb))) => hy.
move: (hy) => [oe _ _].
have ucc:union (cnext C)  = E by rewrite - [union _] (limit_nonsucc hy).
have pc: forall i, inc i (domain S) -> \osup (Vg S i) = E.
   move => i ids; move /(ord_cofinal_p2 hy (h3 _ ids)): (h2 _ ids).
   by rewrite ucc.
have ose: ordinal_set E by move => t /(Os_ordinal oe).
have neS: nonempty S by apply/domain_set0P; exists \0c.
have pd: ord_cofinal T E.
  split => // x xe.
  pose yipp i y := [/\ inc y (Vg S i), x <=o y & forall z,
         inc z (Vg S i) -> x <=o z -> y <=o z].
  pose yis i := Zo (Vg S i) (yipp i).
  pose yi i := intersection (yis i). 
  have yip:forall i, inc i (domain S) -> yipp i (yi i). 
    move => i ids; suff: inc (yi i) (yis i) by move/Zo_hi.
    move: (pc _ ids) => h.
    have xe1 : x <o \osup (Vg S i) by rewrite h; move/(oltP oe): xe.
    have osi: ordinal_set (Vg S i) by move => t /(h3 _ ids) /ose. 
    apply:ordinal_setI; last by move => t /Zo_P [/osi].
    move: (olt_sup osi xe1) => [z za [zb _]]. 
    pose p z := inc z (Vg S i) /\ x <=o z.
    have pz: p z by split.
    have oz:= proj32 zb.
    move: (least_ordinal4 oz pz) => [ta [tb tc] td].  
    have ok: (yipp i (least_ordinal p z)).
      by split => // t te tf; move:(proj32 tf)=> ot; apply: td.
    by exists (least_ordinal p z); apply:Zo_i.
  have yi1: forall i j, inc i (domain S) -> inc j (domain S) -> i <o j ->
     inc (yi j) (Vg S i).
    move => i j ids jds ij; apply: (h4 _ _ ij ids jds).
    by case:(yip _ jds).
  have yi2: forall i j, inc i (domain S) -> inc j (domain S) -> i <o j ->
     (yi i) <=o (yi j).
    move => i j ids jds ij; move: (yi1 _ _ ids jds ij) => h.
    move: (yip _ ids) (yip _ jds) => [_ _ uc] [ _ ub _]; apply: uc => //.
  set F := fun_image (domain S) yi. 
  have cf: cardinal F <=c C. 
    exact:cleT (fun_image_smaller (domain S) yi) cds.
  have fe: sub F E. 
    move => t /funI_P [z zdf ->]; move /yip:(zdf) => [ua ub _].
    by apply: (h3 _ zdf).
  have osf: ordinal_set F by move => t /fe /ose.
  move: (cnext_sup ic cf fe); rewrite -/E => pd.
  have pe: x <=o (union F).
    move:(yip _ pa) => [_ ua _]; apply: (oleT ua); apply: ord_sup_ub => //.
    apply /funI_P; ex_tac.
  exists (\osup F) => //; apply/setIb_P => //. 
  move => i ids.
  set G := fun_image (Zo (domain S) (fun z => i <=o z)) yi.
  have oi:= (Os_ordinal ods ids).
  have pf:inc i (Zo (domain S) [eta ordinal_le i]). 
      apply/Zo_P; split => //; exact: (oleR oi).
  have eq1: \osup G = \osup F.
    apply:ord_sup_1cofinal => //; split.
       move => t /funI_P [z /Zo_P [ha _] ->]; apply/funI_P; ex_tac.
    move => a /funI_P [z za ->].
    have oz:= (Os_ordinal ods za).
    case (oleT_el oi oz) => h5. 
       exists (yi z); first by apply/funI_P; exists z => //; apply/Zo_P => //.
       by move: (yip _ za) => [_ /proj32 /oleR h6 _].
    by exists (yi i); [ apply/funI_P; exists i | apply:yi2 ].
  have g1: sub G (Vg S i). 
    move => t /funI_P [j /Zo_P [ja jb] ->]; case (equal_or_not i j) => ij.
       by rewrite ij; move: (yip _ ja) => [h6 _ _].
    apply:yi1 => //.
  have neg: nonempty G by exists (yi i); apply/funI_P; exists i.
  move:(h1 _ ids) => [sd se]; move: (se _ g1 neg); rewrite eq1.
  case => //;move: (pc _ ids) => -> h6.
  by case: (ordinal_irreflexive oe); move: pd; rewrite h6.
split => //.
have pe: \osup T = E by move /(ord_cofinal_p2 hy pb): pd ->. 
split; first by move => x /pb /(cnextP (proj1 ic)) [].
move => F FT neF; rewrite pe;set x := (\osup F).
case (equal_or_not x E) => xe; [by left | right ].
apply/setIb_P => // i ids; move:(h1 _ ids) => [_ h5].
have h6: sub F (Vg S i) by move => t /FT ts; exact :(setIb_hi ts ids).
move: (h5 _ h6 neF); rewrite (pc _ ids); rewrite - /x; case => //.
Qed.

Definition many_der_aux f E g :=
  Yo (source g = \0o) f
      (ordinalsE E (intersectionf (source g) (fun z => fixpoints (Vf g z)))).

Definition many_der f E :=
  transfinite_defined (ordinal_o E) (many_der_aux f E).

Lemma many_der_ex C (E := cnext C) f (g:= many_der f E)
  (ii:= fun i => (intersectionf i (fun z => fixpoints (Vf g z)))):
  infinite_c C -> normal_function f E E -> 
  [/\ function g, source g = E, Vf g \0o = f, 
      (forall i, inc i E ->  i <> \0o -> Vf g i = ordinalsE E (ii i)) &
       [/\ forall i, inc i E -> i <> \0o ->
          lf_axiom (ordinals (fun x y => [/\ inc x  (ii i), inc y  (ii i) 
        & x <=o y])) E E,
       (forall i, inc i E ->  i <> \0o ->
          iclosed_set (ii i) /\ ord_cofinal (ii i) E),
       (forall i, inc i E -> normal_function (Vf g i) E E) &
       (forall i, inc i E -> i <> \0o ->
         Imf (Vf g i) =  (ii i))]]. 
Proof.
move => pa pb.
have oe: ordinalp E by move:(cnext_pr1 (proj1 pa)) => [[]]. 
case:(transfinite_defined_pr (many_der_aux f E) (ordinal_o_wor oe)).
rewrite -/(many_der _ _) -/g ordinal_o_sr => sa sb sc. 
have ze:= (cnext_leomega pa (proj1 olt_0omega)).  
have fg: function g by fct_tac.
move: (sc _ ze). 
rewrite /many_der_aux /restriction1; aw.
have -> :(segment (ordinal_o E) \0o = \0o) by rewrite ordinal_segment.
Ytac0 => pc.
pose fpi i := fixpoints (Vf g i).
have pd: forall i, inc i E -> i <> \0o -> Vf g i =  ordinalsE E (ii i).
  move => i ie inz; move: (sc _ ie).
  rewrite /many_der_aux {1 2} /restriction1; aw.
  have -> :(segment (ordinal_o E) i = i) by rewrite ordinal_segment.
  Ytac0 ; move => ->; congr (fun z => ordinalsE E z); apply: setIf_exten.
  move => k ki /=; rewrite restriction1_V // sb. 
  apply: (ordinal_transitive oe ie).
split => //.
pose pp k := iclosed_set (fpi k)/\ ord_cofinal (fpi k) E /\ 
   forall l, l <o k -> sub (fpi k) (fpi l).
have pe: forall i, inc i E -> i<> \0o -> (forall k, k <o i -> pp k) ->
  iclosed_set (ii i) /\ ord_cofinal (ii i) E.
  move => i ie inz H.
  set S := Lg i fpi.
  have qa: fgraph S by rewrite /S; fprops.
  have qb: domain S = i by rewrite /S; aw.
  move /(cnextP (proj1 pa)): ie => [u1 u2].
  have qc: ordinalp (domain S) by rewrite qb.
  have qd: cardinal (domain S) <=c C by rewrite qb.
  have qe: nonempty (domain S). 
    by exists \0c;move:(olt_i (ord_ne0_pos u1 inz)); rewrite - qb.
  have qf:(intersectionb S) = ii i.
    rewrite /ii /S /fpi /intersectionb Lgd;apply:setIf_exten => k kd.
    by rewrite LgV.
  move:( closed_cofinal_inter pa qa qc qd qe); rewrite -/E qf qb; apply.
  + by move => k ki; rewrite /S LgV//; move /(oltP u1): ki => /H /proj1.
  + by move => k ki;rewrite /S LgV//; move /(oltP u1): ki => /H /proj2/proj1.
  + move => k j kj ki ji; rewrite /S !LgV//.
    by move /(oltP u1): ji => /H /proj2/proj2; apply.
have pf: forall i, inc i E -> i <> \0o ->
    iclosed_set (ii i) /\ ord_cofinal (ii i) E ->
    normal_function (Vf g i) E E /\ Imf (Vf g i) = ii i.
  move => i ie inz [ta tb]; move: (ordinals_set_normal1 pa ta tb).
  by have -> //: ordinalsE E (ii i) = Vf g i; rewrite pd => //; move => [_].
have pg: forall k, inc k E -> pp k.
  move =>k ke.
  have ok:= Os_ordinal oe ke.
  move: k ok ke; apply:least_ordinal2 =>  l ol etc le.
  have ss: forall i, inc i E -> (source (Vf g i)) = E.
    move => i ie; case: (equal_or_not i \0o) => iz.
      by rewrite iz pc; move: pb => [[]].
    by rewrite (pd i ie iz) /ordinalsE; aw.
  case: (equal_or_not l \0o) => l0.
     have sfe: source f = E by move: pb => [ [] ].
     rewrite l0 /pp/fpi pc; split.
    apply:(iclosed_fixpoints_fun  oe) => //; rewrite sfe.
     split; last by move => m /olt0. 
     by apply: normal_fix_cofinal.
  have ww: forall k, k <o l -> pp k.
    move /(oltP oe): le => lte.
    move => t tl; apply: etc => //;apply/(oltP oe); exact:(olt_ltT tl lte).
  move: (pe _ le l0 ww) => r0; move: (pf l le l0 r0) => [ta tb].
  have tc:  iclosed_set (fpi l). 
     by move: (iclosed_fixpoints_fun oe ta); rewrite /fpi/fixpoints ss.
  have td:  ord_cofinal (fpi l) E by rewrite /fpi; apply: normal_fix_cofinal.
  split => //; split => //.
    move => m lm t.
    have lle : l <o E by apply /oltP.
    have me:=(olt_i(olt_ltT lm lle)).
    rewrite /fpi /fixpoints ss // ss //.
    move => /Zo_P [ua ub]; apply /Zo_P; split => //.
    have fv: function (Vf g l) by move: ta => [[]].
    have ti: inc t (ii l). 
       rewrite - tb; apply /(Imf_P fv); rewrite ss//; exists t => //.
    by move:(setIf_hi ti (olt_i lm)) => /Zo_P [].
have ph: forall i, inc i E -> i <> \0o -> 
  normal_function (Vf g i) E E /\ Imf (Vf g i) = ii i.
  move => i ie inz; apply: pf => //; apply: pe => // k ke; apply: pg.
  have iE: i <o E by apply/oltP. 
  exact:(olt_i(olt_ltT ke iE)).
split.
+  move => i ie inz.
  have [ta tb]:iclosed_set (ii i) /\ ord_cofinal (ii i) E.
     apply: pe => // k ke;apply: pg.
     have iE: i <o E by apply/oltP.
     apply /oltP => //; exact:(olt_ltT ke iE).
  move: (proj1 (ordinals_set_iso (proj1 ta))).
  by rewrite (ord_cofinal_p5 pa) -/E // => h t ti; apply: (proj1 tb); apply: h.
+ move => i ide inz; apply: pe => // k ki; apply: pg.
   have iE: i <o E by apply/oltP.
   apply /oltP => //; exact:(olt_ltT ki iE).
+ move => i ide; case (equal_or_not i \0o);first by move => ->; ue. 
  move => inz; exact: (proj1 (ph i ide inz)).
+ move => i ide inz;exact: (proj2 (ph i ide inz)).
Qed.

Lemma many_der_unique C1 C2 f1 f2 (E1:= cnext C1) (E2:= cnext C2)
   (g1:= many_der f1 E1) (g2:= many_der f2 E2):
  C1 <=c C2 -> infinite_c C1 -> infinite_c C2 ->
  agrees_on E1 f1 f2 ->
  normal_function f1 E1 E1 -> normal_function f2 E2 E2 ->
  forall i, inc i E1 -> agrees_on E1 (Vf g1 i) (Vf g2 i).
Proof.
move => lcc ic1 ic2 agg n1 n2.
have pa: sub E1 E2.
   move => x /(cnextP (proj1 ic1)) [sa sb]; apply/(cnextP (proj1 ic2)).
   split => //;exact: (cleT sb lcc).
move: (many_der_ex ic1 n1). 
move: (many_der_ex ic2 n2).
rewrite -/E1 -/E2 -/g1 -/g2.
set ii1:= fun i => (intersectionf i (fun z => fixpoints (Vf g1 z))).
set ii2:= fun i => (intersectionf i (fun z => fixpoints (Vf g2 z))).
move => [fg2 sg2 g20 g2v [hr2 cc2 ng2 ig2]].
move => [fg1 sg1 g10 g1v [hr1 cc1 ng1 ig1]].
move => i ie1.
have sg1i:source (Vf g1 i) = E1 by move: (ng1 _ ie1) => [[]].
have sg2i:source (Vf g2 i) = E2 by move: (ng2 _ (pa _ ie1)) => [[]].
hnf; rewrite sg1i sg2i; split=> // x xe1; move: x xe1.
have oe1: ordinalp E1 by move:(cnext_pr1 (proj1 ic1)) => [[]].
have oi:= (Os_ordinal oe1 ie1).  clear sg1i sg2i.
move: i oi ie1; apply:least_ordinal2 => y oor etc ye1 x xe1.
case: (equal_or_not y \0o) => ynz.
  by rewrite ynz g10 g20; move: agg => [sa sb sc];rewrite sc.
rewrite g1v // g2v //; last by apply:  pa.
move: (cc1 y ye1 ynz) => [sa sc].
move: (cc2 y (pa _ ye1) ynz) => [sb sd].
have se: (ii1 y) = (ii2 y) \cap  E1.
  have y0:= (olt_i (ord_ne0_pos oor ynz)).
  have yne: nonempty y by exists \0o.
  have lye1: y <o E1 by apply /oltP.
  set_extens t.
    move => ti.
    have te1: inc t E1.
     by move:(setIf_hi ti y0) => /Zo_S; rewrite g10; move: n1 => [[_ -> _ ]].
    apply /setI2_P; split => //.
    apply /setIf_P => // j jy.
    have jy1: j <o y by apply /oltP.
    have je1:= olt_i (olt_ltT jy1 lye1).
    have sj1:  (source (Vf g1 j)) = E1 by move: (ng1 _ je1) => [[]].
    have sj2:  (source (Vf g2 j)) = E2 by  move: (ng2 _ (pa _ je1)) => [[]].
    move:(setIf_hi ti jy) => /Zo_P [za zb]; apply /Zo_P; split => //.
      by rewrite sj2; apply: pa.
    by move: (etc _ jy1 je1 t te1) => <-.
  move => /setI2_P [ti2 te1]; apply /setIf_P => // j jy.
  have jy1: j <o y by apply /oltP.
  have je1:= olt_i (olt_ltT jy1 lye1).
  have sj1:  (source (Vf g1 j)) = E1 by move: (ng1 _ je1) => [[]].
  have sj2:  (source (Vf g2 j)) = E2 by  move: (ng2 _ (pa _ je1)) => [[]].
  move:(setIf_hi ti2 jy) => /Zo_P [za zb]; apply /Zo_P; split => //.
     by rewrite sj1.
   by move: (etc _ jy1 je1 t te1) ->.
move: (ordinals2_extc ic1 ic2 sa sb sc sd lcc se) => [ra rb rc].
by apply: rc.
Qed.


Definition all_der_bound (f: fterm) (b: fterm2):=
  forall x i, ordinalp x -> ordinalp i ->
    [/\ inc x (b x i), inc i (b x i), 
      (exists2 C, infinite_c C & b x i = cnext  C) &
      forall t, inc t (b x i) -> inc (f t) (b x i)].

Lemma all_der_bound_prop f b x i
   (E:= b x i)  (C := (\csup (Zo E cardinalp))):
   ordinalp x -> ordinalp i -> all_der_bound f b ->
   [/\ infinite_c C, inc x E, inc i E, E = cnext C &
    forall t, inc t E -> inc (f t) E].
Proof.
move => ox oi h.
move: (h _ _ ox oi) => [sa sb sc sd].
by move: (cnext_pred_more sc) => [sz sf].
Qed.

Definition all_der_aux (f:fterm) E x i := 
   Vf (Vf (many_der (Lf f E E) E) i) x.

Definition all_der (f:fterm) (b:fterm2) x i := all_der_aux f (b x i) x i.


Section All_derivatives.
Variable f: fterm.
Variable b: fterm2.
Hypothesis nf: normal_ofs f.
Hypothesis bf: all_der_bound f b.
Let g := all_der f b.

Lemma all_der_bound_prop2 x i:
   ordinalp x -> ordinalp i ->
   normal_function (Lf f (b x i) (b x i)) (b x i) (b x i). 
Proof.
move => sa sb; move: (all_der_bound_prop sa sb bf).
move => [ta tb tc td te].
rewrite td in te.
by move:(normal_ofs_restriction ta nf te); rewrite - td.
Qed.

Lemma all_der_p1 x i C (E:= cnext C):
  infinite_c C ->
  inc x E -> inc i E -> (forall t, inc t E -> inc (f t) E) ->
  g x i =  all_der_aux f E x i.
Proof.
move => pc xe ie esf.
move: (proj1 (CS_cnext (proj1 pc))) => oe.
move: (Os_ordinal oe xe) (Os_ordinal oe ie) => ox oi.
have n1:=(all_der_bound_prop2 ox oi).
have n2:=(normal_ofs_restriction pc nf esf).
have aux: forall C C', C <=c C' -> sub (cnext C) (cnext C').
   move => C1 C2 cc; move: (cc) => [c1 c2 _].
   move => t /(cnextP c1) [sa sb]; apply/(cnextP c2).
   by move:(cleT sb cc).
move:(all_der_bound_prop ox oi bf). 
set C1 := union _; move => [sa sb sc sd se].
rewrite {3 4} sd in n1. 
case: (cleT_ee (proj1 pc) (proj1 sa)) => cc.
  have see: sub E (b x i) by rewrite sd;apply: aux.
  have ag: agrees_on E (Lf f E E) (Lf f (b x i) (b x i)).
    by hnf; aw; split => // => t te /=; rewrite !LfV//; apply: see.
  move: (many_der_unique cc pc sa ag n2 n1 ie) => [_ _ h].
  by symmetry;   move: (h _ xe); rewrite - sd.
have see: sub (b x i) E by rewrite sd;apply: aux.
have ag: agrees_on (b x i)  (Lf f (b x i) (b x i)) (Lf f E E).
    by hnf; aw; split => // => t te /=; rewrite !LfV//; apply: see.
rewrite {1} sd in ag; rewrite sd in sb sc.
move: (many_der_unique cc sa pc ag n1 n2 sc)=> [_ _ h].
by move: (h _ sb); rewrite - sd.
Qed.


Lemma all_der_p2 x:  ordinalp x -> g x \0o = f x.
Proof.
move => ox.
have [sb sc sd se sf]:= (all_der_bound_prop ox OS0 bf).
have sa:= (all_der_bound_prop2 ox OS0).
rewrite se in sa.
move:(many_der_ex sb sa) => [pa pb pc _ _]. 
move: (f_equal (Vf^~ x) pc); rewrite - se LfV//.
Qed.

Lemma all_der_p3 x i: ordinalp x -> ordinalp i -> inc (g x i) (b x i).
Proof.
move => ox oi.
have [sb sc sd se sf]:= (all_der_bound_prop ox oi bf).
have sa:= (all_der_bound_prop2 ox oi).
rewrite se in sa.
move:(many_der_ex sb sa) => [_ _ _ _ [_ _ pg _]].
rewrite se in sd.
move: (pg _ sd); rewrite - se; move => [[p1 p2 p3] _ _].
rewrite -p3 /g/all_der/all_der_aux; Wtac. 
Qed.

Lemma OS_all_der x i: ordinalp x -> ordinalp i -> ordinalp (g x i).
Proof.
move=> ox oi; move: (all_der_p3 ox oi) => h.
have [sb _ _ se _]:= (all_der_bound_prop ox oi bf). 
rewrite se in h.
exact: (Os_ordinal (proj1 (CS_cnext (proj1 sb))) h).
Qed.

Lemma all_der_p4 x y i: ordinalp i -> x <o y  -> 
  [/\  inc x (cnext (union (Zo (b y i) cardinalp))),
       g x i = all_der_aux f (b y i) x i &
       g y i = all_der_aux f (b y i) y i].
Proof.
move => oi xy.
move: (xy) => [[ox oy _] _].
have [sa sb sc sd se]:= (all_der_bound_prop oy oi bf).
rewrite sd in sb sc se.
have xe: inc x (cnext (union (Zo (b y i) cardinalp))).
  have ose:= (proj1 (CS_cnext (proj1 sa))).
  move/(oltP ose): sb => lt1.
  apply/(oltP ose); apply: olt_ltT xy lt1.
rewrite (all_der_p1 sa xe sc se); split => //.
rewrite /g /all_der - sd//.
Qed.

Lemma all_der_p5 x y i: ordinalp i -> x <o y  -> g x i <o g y i.
Proof.
move => oi xy.
have [xe v1 v2]:=(all_der_p4 oi xy).
have [[ox oy _] _] := xy.
have [sa sb sc sd se]:= (all_der_bound_prop oy oi bf).
move: (all_der_bound_prop2 oy oi);  rewrite sd => sf.
rewrite sd in sb sc se.
move:(many_der_ex sa sf) => [_ _ _ _ [_ _ ug _]].
move: (ug _ sc) => [ua ub _];move: (ub _ _ xe sb xy).
rewrite - sd v1 v2//.
Qed.

Lemma all_der_p5' x y i: ordinalp i -> ordinalp x -> ordinalp y  ->
  g x i = g y i ->  x = y.
Proof.
move => oi ox oy h.
by case: (oleT_ell ox oy) => // /(all_der_p5 oi) []; rewrite h.
Qed.

Lemma all_der_p5'' x y i: ordinalp i -> ordinalp x -> ordinalp y  ->
  g x i <o g y i ->  x<o y.
Proof.
move => oi ox oy h.
case: (oleT_ell oy ox) => //. 
  by move => eq; move: (proj2 h); rewrite eq.
by move/(all_der_p5 oi) => [/(oltNge h)].
Qed.

Lemma all_der_p6 i: ordinalp i -> normal_ofs (g ^~i).
Proof.
move => oi.
split; first by move => x y xy;apply:all_der_p5.
move => x lx.
move: (lx) => [ox _ _].
have osx: forall y, inc y x -> y <o x by move => y /(oltP ox).
pose g1 y := all_der_aux f (b x i) y i.
have -> : g x i = g1 x by [].
have -> : fun_image x (g^~ i) = fun_image x g1.
  have h: forall z, inc z x ->  g z i = g1 z.
     move => z zx.
     have zx': z <o x by apply/(oltP ox).
     by move: (all_der_p4 oi zx') => [_ -> _].
  by set_extens t; move =>/funI_P [z zx ->]; apply/funI_P; ex_tac; rewrite h.
have [sa sb sc sd se] := (all_der_bound_prop ox oi bf).
move: (all_der_bound_prop2 ox oi);  rewrite sd => sf.
move:(many_der_ex sa sf) => [_ _ _ _ [_ _ ug _]].
rewrite - sd in ug.
move: (ug _ sc); set g2 := (Vf _ _).
have <-: Vf g2 x = g1 x by [].
move => [[ fg2 sg2 _] hb hc]; rewrite (hc _ sb lx); congr union.
have sgx: sub x (source g2). 
   rewrite sg2;apply:ordinal_transitive => //; rewrite sd.
   exact: (proj1 (CS_cnext (proj1 sa))).
set_extens t.
  move/(Vf_image_P fg2 sgx) => [u ut ->]; apply/funI_P; ex_tac.
move /funI_P=> [u ut ->]; apply /(Vf_image_P fg2 sgx); ex_tac.
Qed.

Lemma all_der_p7 x i j: ordinalp x -> i <o j ->  g (g x j) i = g x j.
Proof.
move => ox ij.
move: (ij) => [[oi oj _] _].
move: (all_der_bound_prop ox oj bf).
set C:= union _; set E:= cnext C.
move => [sa sb sc sd se].
rewrite sd in sb sc se.
have ie: inc i E.
  move: (proj1 (CS_cnext (proj1 sa))) => ose.
  move/(oltP ose): sc => /(olt_ltT ij) lt1.
  by apply/(oltP ose).
set ge:= all_der_aux f E.
set y := (g x j).
have ye: inc y E by rewrite - sd; apply:all_der_p3.
have v1:= (all_der_p1 sa ye ie se).
have v2:= (all_der_p1 sa sb sc se). 
have jnz: j <> \0o by move => h; move: ij; rewrite h; exact:olt0.  
move: (all_der_bound_prop2 ox oj); rewrite sd => sf.
move:(many_der_ex sa sf); rewrite -/E.
set ff:=(many_der (Lf f E E) E).
move => [ua ub uc ud [_ _ ug uh]].
have h:= (ud _ sc jnz).
have v3: y = Vf (Vf ff j) x by rewrite /y v2.
move: (ug _ sc) => [[pa pb pc] _ _].
have ij': inc i j by apply/oltP => //.
have: inc y (Imf (Vf ff j)).
    rewrite v3; apply/(Imf_P pa); exists x => //; ue.
rewrite (uh j sc jnz) v1 => h1.
by move: (setIf_hi h1 ij') => /Zo_hi.
Qed.

Lemma all_der_p8 y j: ordinalp y -> \0o <o j ->
   (forall i, i <o j ->  g y i = y) ->
   (exists2 x, ordinalp x & y = g x j).
Proof.
move => oy jp h.
have oj:=proj32_1 jp.
have jnz:= nesym (proj2 jp).
move: (all_der_bound_prop oy oj bf).
set C:= union _; set E:= cnext C.
move => [sa sb sc sd se].
move: (all_der_bound_prop2 oy oj);  rewrite sd => sf.
rewrite sd in sb sc se.
move:(many_der_ex sa sf); rewrite -/E.
set ff:=(many_der (Lf f E E) E).
move => [ua ub uc ud [_ _ ug uh]].
move: (proj1 (CS_cnext (proj1 sa))) => oe.
suff:inc y (Imf (Vf ff j)).  
  move: (ug _ sc) => [[pa pb pc] _ _ ].
  move /(Imf_P pa); rewrite pb; move => [u ue uv]; exists u.
     exact: (Os_ordinal oe ue).
  by rewrite uv (all_der_p1 sa ue sc). 
rewrite (uh j sc jnz).
have nej: nonempty j by exists \0o;move: (olt_i jp).
apply /setIf_P => // i ij.
have ij1: i <o j by apply/(oltP oj).
have iE: inc i E. by move/(oltP oe): sc => /(olt_ltT ij1) /olt_i.  
move: (ug _ iE) => [[pa pb pc] _ _ ].
apply /Zo_P; rewrite pb; split => //.
by move:(h _ ij1);rewrite (all_der_p1 sa sb iE se). 
Qed.

Lemma all_der_p9 x y i j: 
  ordinalp x -> ordinalp y -> ordinalp i -> ordinalp j ->
  (g x i = g y j  <->
   [/\ i <o j -> x = g y j, i = j -> x = y & j <o i -> y = g x i]).
Proof.
move => ox oy oi oj.
case (oleT_ell oi oj).
+ move => ->.
  split; last by move => [_ ok _]; rewrite (ok (erefl j)).
  move /(all_der_p5' oj ox oy) => xy.
  by split => // [] [].
+ move => lij.
  move: (all_der_p7 oy lij) => eq1.
  split.
    rewrite - {1} eq1; move /(all_der_p5' oi ox (OS_all_der oy oj)) => <-.
    split => //.
    - by move => ii; move: (proj2 lij); rewrite ii.
    - by move => [/(oltNge lij) ].
  by move => [h _ _]; rewrite (h lij).
+ move => lji.
  move: (all_der_p7 ox lji) => eq1.
  split.
    rewrite - {1} eq1 => eq; symmetry in eq. 
    rewrite - (all_der_p5' oj oy (OS_all_der ox oi) eq).
    split => //.
    - by move => [/(oltNge lji) ].
    - by move => ii; move: (proj2 lji); rewrite ii.
  by move => [_ _ h]; rewrite (h lji).
Qed.


Lemma all_der_p10 x y i j: 
  ordinalp x -> ordinalp y -> ordinalp i -> ordinalp j ->
  (g x i <o g y j  <->
   [/\ i <o j -> x <o g y j, i = j -> x <o y & j <o i -> g x i <o y]).
Proof.
move => ox oy oi oj.
case (oleT_ell oi oj).
+ move => ->; split.
  by move /(all_der_p5'' oj ox oy) => h; split => // [][].
  move => [_ ok _]; exact: (all_der_p5 oj (ok (erefl j))).
+ move => lij.
  move: (all_der_p7 oy lij) => eq1.
  split.
    rewrite - {1} eq1; move /(all_der_p5'' oi ox (OS_all_der oy oj)) => h1.
    split => //.
    - by move => ii; move: (proj2 lij); rewrite ii.
    - by move => [/(oltNge lij)].
    - by move => [h _ _]; rewrite - eq1; apply:all_der_p5 => //; apply:h.
+ move => lji.
  move: (all_der_p7 ox lji) => eq1.
  split.
    rewrite - {1} eq1; move /(all_der_p5'' oj (OS_all_der ox oi) oy) => h1.
    split => //.
    - by move => [/(oltNge lji)].
    - by move => ii; move: (proj2 lji); rewrite ii.
    - by move => [_ _ h]; rewrite - eq1; apply:all_der_p5 => //; apply:h.
Qed.


Lemma all_der_p10' x y i j: 
  ordinalp x -> ordinalp y -> ordinalp i -> ordinalp j ->
  (g x i <=o g y j  <->
   [/\ i <o j -> x <=o g y j, i = j -> x <=o y & j <o i -> g x i <=o y]).
Proof.
move => ox oy oi oj.
move: (all_der_p9 ox oy oi oj) (all_der_p10 ox oy oi oj) => ha hb.
case: (equal_or_not (g x i) (g y j)) => h2.
  move/ha:(h2) => [sa sb sc].
  split => // _. 
    split => // h3.
    + rewrite - (sa h3); fprops.
    + rewrite - (sb h3); fprops.
    + rewrite - (sc h3); fprops.
  by rewrite h2; apply: oleR; apply:OS_all_der.
split => h.
  move/hb: (conj h h2) => [sa sb sc].
    split => // h3.
    + exact: (proj1 (sa h3)).
    + exact: (proj1 (sb h3)).
    + exact: (proj1 (sc h3)).
have[//]: g x i <o g y j.
move:h => [sa sb sc].
apply/ hb; split => // h3; split; fprops => ne; case h2; apply /ha.
+ split => //. 
    by move => ii; move: (proj2 h3); rewrite ii.
  by move => [/(oltNge h3)].
+  by rewrite h3; split => // [] [].
+ split => //.
  by move => [/(oltNge h3)].
  by move => ii; move: (proj2 h3); rewrite ii.
Qed.

Lemma all_der_p11 x i j : ordinalp x -> i <=o j -> g x i <=o g x j.
Proof.
move => ox ij.
move: (ij) => [oi oj _].
apply/(all_der_p10' ox ox oi oj); split => //.
+ move => lij.
  exact: (osi_gex (proj1 (all_der_p6 oj))  ox).
+ move => _; fprops.
+ by move => /(oleNgt ij).
Qed.


Lemma all_der_p12 i : ordinalp i -> f \0o = \0o -> g \0o i = \0o.
Proof.
move => oi f0. move: i oi; apply least_ordinal2 => y oy etc.
case: (ozero_dichot oy) => yz; first by rewrite yz all_der_p2 //; fprops.
move: (all_der_p8 OS0 yz etc)=> [x ox h].
case (ozero_dichot ox) => xz; first by rewrite - {1} xz.
by move: (all_der_p5 oy xz); rewrite - h; move /olt0. 
Qed.

Lemma all_der_p13 : f \0o <> \0o -> normal_ofs (g \0o).
Proof.
move => fz.
have pa: forall i j, i <oj -> g \0o i <o g \0o j.
  move => i j ij;move:(ij)=> [[oi oj _] _].
  apply/(all_der_p10 OS0 OS0 oi oj); split => //.
  + move => _; apply: ord_ne0_pos; first by apply:(OS_all_der OS0 oj).
    move => eq1; move:(all_der_p7 OS0 (ole_ltT (ole0x oi) ij)).
    by rewrite eq1  (all_der_p2 OS0).
  + by move: (proj2 ij).
  + by move => [/(oltNge ij)].
split => // j lj.
move: lj => [oj z0j lj1].
have osi: ordinal_set (fun_image j (g \0o)).
  move => t /funI_P [i ij ->]; apply:OS_all_der; fprops. 
  exact: (Os_ordinal oj ij).
have oy: (ordinalp (g \0o j)) by apply:OS_all_der; fprops.
have ubb: ordinal_ub (fun_image j (g \0o)) (g \0o j).
  move =>  t /funI_P [i ij ->].
  have ij1: i <o j by apply/(oltP oj).
  exact (proj1 (pa _ _ ij1)).
set ww := \osup (fun_image j (g \0o)).
pose Tk k := (fun_image (Zo j (fun z => k <o z)) (g \0o)).
have wa: forall k, k <o j -> inc (g \0o (osucc k)) (Tk k).
  move => k kj.
  have ikj: inc k j by apply/oltP.
  move:(lj1 _ ikj) => kj1.
  apply/funI_P; exists (osucc k) => //; apply/Zo_P; split => //.
  apply: (oltS (proj31_1 kj)).
have pc: forall k, k <o j -> \osup (Tk k) = ww.
  move => k kj.
  apply: ord_sup_1cofinal => //; split.
    move => t /funI_P [z /Zo_S zj ->]; apply/funI_P; ex_tac.
  move => x /funI_P [z zj ->].
  move: (Os_ordinal oj zj) (proj31_1 kj) => oz ok.
  case (oleT_el oz ok) => kz.
    exists (g \0o (osucc k)); first by exact:(wa _ kj).
    by move /oltSleP: kz => /pa [].
  exists (g \0o z); first by apply/funI_P; exists z => //;apply/Zo_P.
  apply: oleR; apply:OS_all_der; fprops.
move: (all_der_bound_prop OS0 oj bf).
set C:= union _; set E:= cnext C.
move => [sa sb sc sd se].
rewrite sd in sb sc se.
move: (all_der_bound_prop2 OS0 oj);  rewrite sd => sf.
move:(many_der_ex sa sf); rewrite -/E.
set ff:= (many_der (Lf f E E) E).
pose ii i:= (intersectionf i (fun z : Set => fixpoints (Vf ff z))).
move=> [ua ub uc _ [_ _ ug uh]].
have oe:= proj1(CS_cnext (proj1 sa)).
have lje: j <o E by apply/(oltP oe).
have wwe: inc ww E.
  have p1:sub (fun_image j (g \0o)) E.
     move => t /funI_P [z za ->].
     have ze:=(ordinal_transitive oe sc za).
     move: (ug _ ze) => [[fg sg tg] _ _].
     rewrite (all_der_p1 sa sb ze se). 
     rewrite -tg -/E /all_der_aux -/ff; Wtac.
   apply: cnext_sup => //.
   move/(cnextP (proj1 sa)):sc => [_ rd].
   exact: (cleT (fun_image_smaller j (g \0o)) rd).
have pd: forall k, k<o j ->  ww = g ww k.
  move => k kj; rewrite - (pc _ kj).
  have pr1: forall x, inc x (Tk k) -> x = g x k.
    move => x /funI_P  [i /Zo_P [va vb]  eq].
    by move: (all_der_p7 OS0 vb); rewrite - eq.
  set Z:= fun_image  (Tk k) (g^~k).
  have h1: Tk k = Z.
       set_extens t. 
          move => tk; move:(pr1 t tk) => eq1; apply/funI_P; ex_tac.
       by move => /funI_P [z za zb]; move: (pr1 _ za); rewrite - zb => <-.
  have nez: nonempty Z by rewrite - h1; move: (wa _ kj) => h; ex_tac.
  have h2: forall x, inc x Z -> \0o <=o x.
    rewrite -h1; move => x /funI_P [i /Zo_P[ta tb] ->].
    exact: (ole0x (OS_all_der OS0 (proj32_1 tb))).
  move: (all_der_p6 (proj31_1 kj)) => na.
  move/normal_ofs_equiv1: na => [_ h3].
  by move: (h3 _ h2 nez); rewrite - h1 -/Z - h1.
have pe: inc ww (Imf (Vf ff j)).
   have nej: nonempty j by ex_tac.
   case:(equal_or_not j \0o) => jnz; first by move: z0j; rewrite jnz;case;case.
   rewrite (uh _ sc jnz); apply/setIf_P => // k kj.
   have lkj: k <o j by apply/(oltP oj).
   have ke:= (olt_i(olt_leT lkj (proj1 lje))).
   move: (ug _ ke) => [[va vb vc] _ _ ].
   have eq1: Vf (Vf ff k) ww = ww.
     by symmetry;rewrite {1} (pd _ lkj) (all_der_p1 sa wwe ke se).
   by apply/Zo_P; rewrite vb.
move: (ug _ sc) => [[va vb vc] _ _ ].
move /(Imf_P va): pe; rewrite vb; move => [u ue eq2].
have eq3: ww = g u j by rewrite (all_der_p1 sa ue sc se) eq2.
move: (ord_ub_sup oy ubb);rewrite -/ww eq3 => h.
case: (equal_or_not u \0o) => uz; first by rewrite uz.
have luz:=(ord_ne0_pos (Os_ordinal oe ue) uz).
case: (oltNge (all_der_p5 oj luz) h).
Qed.


Lemma all_der_p14 i: ordinalp i ->
  first_derivation (g ^~i) =1o g ^~(osucc i).
Proof.
move=> oi.
have sa:= (first_derivation_p0 (all_der_p6 oi)).
have sb:= (all_der_p6 (OS_succ oi)).
move: (proj1 sa)(proj1 sb) => ia ib.
move: (first_derivation_p (all_der_p6 oi))=> [sc sd].
apply:sincr_ofs_exten => // x ox.
  move:(sc _ ox); set y := first_derivation (g^~ i) x => h.
  have snz:= (olt0S oi).
  have oxx:=(ofs_sincr ia ox).
  apply: all_der_p8 => // j jsi.
  case (equal_or_not j i) => eji; first by rewrite eji.
  have ji: j <o  i by move /oltSleP: jsi => h1.
  by move: (all_der_p7 oxx ji); rewrite -/y h.
have oy:=(OS_all_der ox (OS_succ oi)).
have se:= (all_der_p7  ox (oltS oi)).
exact: (sd _ oy se).
Qed.

End All_derivatives.

Lemma all_der_p12_bis f b (g:= all_der f b) z: 
  normal_ofs f ->all_der_bound f b ->
  ordinalp z -> (forall x, x <o z -> f x = x) ->
  (forall x i, x <o z -> ordinalp i -> g x i = x).
Proof.
move => ha hb oz fp x i xi oi0;move:x xi.
move: i oi0; apply: least_ordinal2 => i oi etc x xz.
have ox:= proj31_1 xz.
case (ozero_dichot oi) => iz.
  by rewrite iz /g (all_der_p2 ha hb ox) (fp _ xz). 
have hc: forall x, x <o z -> exists2 t, t <=o x & x = g t i.
  move => u uz.
  have ou:= proj31_1 uz.
  have hh: forall k, k<o i -> g u k = u by move => k ki; move: (etc _ ki _ uz).
  move:(all_der_p8 ha hb ou iz hh) => [t ot]; rewrite -/g => eq1.
  move: (proj1 (all_der_p6 ha hb oi)) => hc.
  by move:(osi_gex hc ot); rewrite -/g - eq1 => tu; exists t.
apply: (least_ordinal2(p:= fun x => x<o z -> g x i = x)) ox (xz) => x0 ox0 etc2.
move => le2.
move: (hc _ le2) => [t ta eq1].
case (equal_or_not t x0) => eq2; first by rewrite - eq2 - eq1.
by move: (etc2 _ (conj ta eq2) (ole_ltT ta le2)) => eq3;rewrite  eq1 eq3.
Qed.

Lemma all_der_p13_bis f b (g:= all_der f b) z: 
  normal_ofs f ->all_der_bound f b ->
  ordinalp z -> (forall x, x <o z -> f x = x) ->
  f z <> z -> normal_ofs (g z).  
Proof.
move => ha hb oz hc fzz.
move: (all_der_p12_bis ha hb oz hc) => hd.
set fs := (fun t => f (z +o t) -o z).
move: (normal_shift ha oz);rewrite -/fs => ha'.
pose bs x i := b (z +o x) i.
have hb': all_der_bound fs bs.
  move => x i ox oi; move:(hb _ _ (OS_sum2 oz ox) oi);rewrite /bs.
  move => [pa pb pc pd]; move: (pc) => [C ic eq].
  have oE := (proj1 (CS_cnext (proj1 ic))).
  rewrite eq in pa;move/(oltP oE): pa => pa'.
  have zE: inc z (b (z +o x) i).
    by move: (ole_ltT(osum_Mle0 oz ox) pa')=> pa''; rewrite eq; apply/(oltP oE).
  have pe: inc x (b (z +o x) i).
    by move: (ole_ltT(osum_M0le oz ox) pa')=> pa''; rewrite eq; apply/(oltP oE).
  split => // t tE. 
  have: inc (z +o t) (b (z+o x) i).
    move: zE tE; move: (cnext_sum ic); rewrite -eq; apply.
  move/pd; rewrite eq; move/(oltP oE) => za; apply /(oltP oE).
  exact: (ole_ltT (odiff_Mle oz (proj31_1 za)) za). 
have zfz: z <o f z.
  split; fprops; exact: (osi_gex (proj1 ha) oz).
have fsz: fs \0o <> \0o.
  by rewrite /fs (osum0r oz) => h; move: (odiff_pos zfz) => []; rewrite h.
move: (all_der_p13 ha' hb' fsz) => he.
set gs:= (all_der fs bs).
have ns:= (osum_normal oz).
suff: forall i, ordinalp i -> forall x, ordinalp x -> 
  z +o (gs x i) = g (z +o x) i.
  move => h.
  have n1: forall i, ordinalp i -> g z i = z +o (gs \0o i).
    by move => i oi; move: (h i oi \0o OS0); rewrite (osum0r oz).
  move: (normal_ofs_compose ns he).
  by apply:normal_ofs_from_exten => t ot /=; rewrite - n1.
apply: least_ordinal2  => i oi etc.
have pa: forall f x, normal_ofs f -> ordinalp x ->
    (ordinalp (f (z +o x) -o z) /\ z +o (f (z +o x) -o z) = f (z +o x)).
  move => h x [sih _] ox; move:(osi_gex sih (OS_sum2 oz ox))=> xh.
  by move: (odiff_pr (oleT (osum_Mle0 oz ox) xh)) => [].
move => x ox.
have na: normal_ofs (fun x => z +o gs x i).
  exact: (normal_ofs_compose ns (all_der_p6 ha' hb' oi)).
have nb: normal_ofs (fun x => g (z +o x) i).
  exact: (normal_ofs_compose (all_der_p6 ha hb oi) ns).
case (ozero_dichot oi) => iz.
   have ozx: ordinalp (z +o x) by fprops.
   rewrite iz /g /gs (all_der_p2 ha hb ozx) (all_der_p2 ha' hb' ox).
   apply: (proj2 (pa _ _ ha ox)).
have ee: forall y j, j <o i -> ordinalp y -> z +o gs y j = g (z +o y) j.
  by move => y j ji oy; move:(etc _ ji _ oy).
move: x ox.
apply:(sincr_ofs_exten (proj1 na) (proj1 nb)) => x ox.
  move: (ofs_sincr (proj1 na) ox) => o1.
  have ot: (ordinalp (gs x i)) by apply: (OS_all_der ha' hb' ox oi).
  have h: forall j, j <o i -> g (z +o gs x i) j = z +o gs x i.
    move => j ji.     
    by rewrite - (ee _ _ ji ot) /gs (all_der_p7 ha' hb' ox ji).
  move: (all_der_p8 ha hb o1 iz h) => [y y1 y2]; rewrite y2 -/g.
  case: (oleT_el oz y1) => eq1.
    by move: (odiff_pr eq1) => [sa sb]; exists (y -o z) => //; rewrite - sb.
  by move: y2 (osum_Mle0 oz ot);rewrite (hd _ _ eq1 oi) => -> /(oltNge eq1).
set u :=(g (z +o x) i -o z).
move: (pa _ x (all_der_p6 ha hb oi) ox) => []; rewrite -/g -/u => [ou uv].
have h: forall j, j <o i -> all_der fs bs u j = u.
  move => j ji. 
  have ogu:= (OS_all_der ha' hb' ou (proj31_1 ji)).
  apply: (osum2_simpl ogu ou oz); rewrite ee // uv.
  exact:(all_der_p7 ha hb (OS_sum2 oz ox) ji). 
rewrite - uv.
by move: (all_der_p8 ha' hb' ou iz h) => [y oy ->]; exists y.
Qed.


Lemma all_der_p13_ter f b (g:= all_der f b): 
  normal_ofs f -> all_der_bound f b ->
  f \0o = \0o -> f \1o <> \1o -> normal_ofs (g \1o).  
Proof.
move => ha hb hc hd; apply:(all_der_p13_bis) => //; fprops.
by move => x /olt1 ->.
Qed.


Lemma all_der_unique f1 f2 b1 b2 
   (g1:=  all_der f1 b1) (g2:=  all_der f2 b2):
   normal_ofs f1 -> all_der_bound f1 b1 -> all_der_bound f2 b2 ->
   (f1 =1o f2) ->
   (forall x i, ordinalp x -> ordinalp i -> g1 x i = g2 x i).
Proof.
move => nf1 h1 h2 sv.
have nf2 := (normal_ofs_from_exten sv nf1).
move => x i ox oi; move: i oi x ox; apply:least_ordinal2 => y oy etc.
case: (ozero_dichot oy) => yp.
  rewrite  yp => x ox. 
  by rewrite /g1 /g2 (all_der_p2 nf1 h1 ox)(all_der_p2 nf2 h2 ox) sv.
move: (all_der_p6 nf1 h1 oy); rewrite -/g1; move=> [pa _].
move: (all_der_p6 nf2 h2 oy); rewrite -/g2; move=> [pb _].
apply:(sincr_ofs_exten pa pb) => x ox.
  move:(ofs_sincr pa ox) => sa.
  apply:(all_der_p8 nf2 h2 sa yp).
  move => j jy; rewrite -/g2 - (etc j jy _ sa). 
  exact :(all_der_p7 nf1 h1 ox jy). 
move:(ofs_sincr pb ox) => sa.
apply:(all_der_p8 nf1 h1 sa yp).
move => j jy;rewrite -/g1 (etc j jy _ sa).
exact :(all_der_p7 nf2 h2 ox jy). 
Qed.


End Ordinals2.
Export Ordinals2.
