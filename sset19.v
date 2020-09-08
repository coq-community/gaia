(** * Theory of Sets  E III.7  Inverse and Direct Limits
  Copyright INRIA (2009-2013) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset19.v,v 1.7 2018/09/04 07:58:00 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat. 
Require Export sset10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Limits.

Lemma ext_to_prod_comp A B C A' B' C' f g f' g':
  inc f (functions A B) -> inc f' (functions A' B') ->
  inc g (functions B C) -> inc g' (functions B' C') ->
  (g \ftimes g') \co (f \ftimes f') = (g \co  f) \ftimes (g' \co f').
Proof.
move => /functionsP[ff _ tf]/functionsP[ff' _ tf'].
move => /functionsP[fg sg _]/functionsP[fg' sg' _].
apply: compose_ext_to_prod2; split => //; ue.
Qed.


Lemma ext_to_prod_comp_bis A B C A' B' C' f g f' g':
  function_prop f A B -> function_prop f' A' B' ->
  function_prop g B C -> function_prop g' B' C' ->
  (g \ftimes g') \co (f \ftimes f') = (g \co  f) \ftimes (g' \co f').
Proof.
move => [ff _ tf] [ff' _ tf'] [fg sg _]  [fg' sg' _].
apply: compose_ext_to_prod2; split => //; ue.
Qed.
  
Record projective_system: Type := ProjectiveSystem {
  psE : Set;
  psI : Set;
  psr : Set;
  psf : Set;
  ps_preorder_r: preorder psr;
  ps_substrate_r: substrate psr = psI;
  ps_fgraph_E: fgraph psE;
  ps_domain_E: domain psE = psI;
  ps_fgraph_f: fgraph psf;
  ps_domain_f: domain psf = psr;
  ps_function_f:
    forall i, inc i psr ->
              function_prop (Vg psf i) (Vg psE (Q i)) (Vg psE (P i));
  ps_compose_f: forall i j k, gle psr i j -> gle psr j k ->
                  Vg psf (J i j) \co  Vg psf (J j k) = Vg psf (J i k);
  ps_identity_f: forall i, inc i psI -> Vg psf (J i i) = identity (Vg psE i)
}.


Definition projective_system_on S E I r f :=
  [/\  psE S = E, psI S = I, psr S = r & psf S = f].


Definition prl_same_data S S' := 
 [/\ psE S = psE S', psr S = psr S' & psf S = psf S'].


Lemma prl_same_dataS S S':
  prl_same_data S S' -> prl_same_data S' S.
Proof. by move => [pa pb pc]. Qed.

Lemma prl_same_dataT S S' S'' :
  prl_same_data S S' -> prl_same_data S' S'' -> prl_same_data S S''.
Proof.
by rewrite /prl_same_data; move => [-> -> ->]. 
Qed.


Definition prl_same_index S S' := psr S = psr S'.

Lemma prl_same_index_same_I S S': 
  prl_same_index S S' -> psI S = psI S'.
Proof. by rewrite - !ps_substrate_r => ->. Qed.

Lemma prl_prop0 S i j: gle (psr S) i j -> inc i (psI S) /\ inc j (psI S).
Proof.
move=> h; rewrite - ps_substrate_r; split; order_tac.
Qed.


Lemma prl_prop1 S i: inc i (psI S) -> inc (J i i) (psr S).
Proof.
move => iI.
by apply:(proj32 (ps_preorder_r S)); rewrite ps_substrate_r.
Qed.

Lemma prl_prop2 S i j k: gle  (psr S) i j -> gle (psr S) j k ->
   Vg (psf S) (J i j) \coP Vg (psf S) (J j k).
Proof.
rewrite /composable.
by move => /ps_function_f [fa -> _] /ps_function_f [fb _ ->]; aw.
Qed.

Lemma prl_prop3 S y i j k (f:= psf S):
  gle (psr S) i j -> gle (psr S) j k -> inc y (Vg (psE S) k) ->
  Vf (Vg f (J i j))  (Vf (Vg f (J j k)) y) = Vf (Vg f (J i k)) y.
Proof.
move => lij ljk yv.
have co:= (prl_prop2 lij ljk).
move:(f_equal (Vf^~ y) (ps_compose_f lij ljk)); rewrite !compfV//.
by move:(ps_function_f ljk) => [_ -> _]; aw.
Qed.

Lemma prl_prop4 S i j: gle (psr S) i j -> 
  function_prop (Vg (psf S) (J i j)) (Vg (psE S) j) (Vg (psE S) i).
Proof.
by move/(ps_function_f); aw.
Qed.

Lemma prl_prop5 S i x: inc i (psI S) -> inc x (Vg (psE S) i) ->
   Vf (Vg (psf S) (J i i)) x = x.
Proof.
by move => iI xE; rewrite (ps_identity_f iI) idV.
Qed.
  
Definition projective_limit S:=
  Zo (productb (psE S)) (fun x => forall i j, gle (psr S) i j
                               -> (Vg x i) = Vf (Vg (psf S) (J i j)) (Vg x j)).

Definition prl_can_fun S i  :=
  Lf (fun x => Vg x i) (projective_limit S) (Vg (psE S) i).

Lemma prl_limitP S x:
  inc x (projective_limit S) <->
  [/\ fgraph x, domain x = psI S,
     forall i, inc i (psI S) -> inc (Vg x i) (Vg (psE S) i)&
   forall i j, gle (psr S) i j -> Vg x i = Vf (Vg (psf S) (J i j)) (Vg x j)].
Proof.
rewrite - ps_domain_E; split.
  by move => /Zo_P [/setXb_P [pa pb pc] pd]. 
by move => [pa pb pc pd]; apply/Zo_P; split => //; apply/setXb_P.
Qed.
  

Lemma prl_proj_ax S i: inc i (psI S) ->
  lf_axiom (fun x => Vg x i) (projective_limit S) (Vg (psE S) i).
Proof.
by move => ide x /prl_limitP[_ _ p3 _]; apply: p3.
Qed.

Lemma prl_proj_ev S i x: inc i (psI S) -> inc x (projective_limit S) ->
   Vf (prl_can_fun S i) x = Vg x i.
Proof.                         
by move => ha hb;rewrite /prl_can_fun LfV//; apply:prl_proj_ax.
Qed.

Lemma prl_can_fun_fp S i: inc i (psI S) ->
  function_prop (prl_can_fun S i) (projective_limit S) (Vg (psE S) i).
Proof.
move => ide; rewrite /prl_can_fun.
saw; apply:lf_function; exact:prl_proj_ax.
Qed.

Lemma prl_can_fun_prop S i j (f := psf S)
      (fi := prl_can_fun S i) (fj := prl_can_fun S j):
   gle (psr S) i j ->
   (Vg f (J i j) \coP fj) /\  fi = (Vg f (J i j)) \co fj.
Proof.
move => lij.
have [fij sij tij]:=(prl_prop4 lij).
have [iE jE]:= (prl_prop0 lij).
have [ffi si ti] := (prl_can_fun_fp iE).
have [ffj sj tj] := (prl_can_fun_fp jE).
have pd: source (Vg f (J i j)) = target fj by rewrite sij.
have pe: Vg f (J i j) \coP fj by [].
have pf:=(compf_f pe).
have pg: source fi = source fj by rewrite si sj.
have ph: target fi = target (Vg f (J i j)) by ue.
split => //;apply:function_exten => //; aw; trivial => x xsf.
rewrite compfV //; last by ue.
have xE: inc x (projective_limit S) by rewrite - si.
rewrite /fi /fj (prl_proj_ev iE xE) (prl_proj_ev jE xE).
by move/Zo_P:xE => [_]; apply.
Qed.


Lemma projective_limit_Iv S S':
  prl_same_data S S' -> projective_limit S = projective_limit S'.
Proof.
by move => [sa sb sc]; rewrite /projective_limit sa sb sc.
Qed.

Lemma prl_can_fun_Iv S S' i: prl_same_data S S' ->
  prl_can_fun S i = prl_can_fun S' i.
Proof.
move=> H; rewrite /prl_can_fun (projective_limit_Iv H). 
by rewrite (proj31 H).
Qed.


Lemma prl_trivial S: psI S = emptyset ->
  projective_limit S = singleton emptyset.
Proof.
move => h.
set_extens t.
move => /prl_limitP[fgt dt _ _ ].
  rewrite - (Lg_recovers fgt) dt h /Lg funI_set0; fprops.
move/set1_P => ->; apply /prl_limitP; split => //.
- apply: fgraph_set0.
- by rewrite domain_set0.
- by rewrite h => i /in_set0.
- by move => i j /prl_prop0 []; rewrite h => /in_set0.
Qed.

Section Example1.
Variables E I: Set.
Hypotheses (fgE:fgraph E) (dE: domain E = I).

Definition prl_exa1_system:projective_system.
Proof.
apply:(@ProjectiveSystem E I (diagonal I)
                           (Lg (diagonal I) (fun z => identity (Vg E (P z))))).
- by move: (diagonal_osr I)=> [/order_preorder].
- by move: (diagonal_osr I)=> [].
- done.
- done.  
- fprops.
- by aw.
- move => i id; move/diagonal_i_P:(id)=> [qa qb qc].
  by rewrite LgV// - qc; exact:identity_prop.
  move => i j k ha hb.
  move: (ha)(hb)=> /diagonal_pi_P [iI eq1]/diagonal_pi_P [_ eq2].
  rewrite - {2} eq2 !LgV // - eq1;  aw; exact:compf_id_id. 
- by move => i iI; rewrite LgV//; aw; trivial; apply/diagonal_pi_P.
Defined.

Lemma prl_exa1_prop:
  projective_system_on prl_exa1_system
  E I (diagonal I)  (Lg (diagonal I) (fun z => identity (Vg E (P z)))).
Proof. by []. Qed.

Lemma prl_exa1_prop2: projective_limit prl_exa1_system = productb E.
Proof.
set_extens t; [ by case/Zo_P | move => tp; apply:(Zo_i tp)].
move => i j ilj; move/diagonal_pi_P:(ilj) => [iI ea]; rewrite - ea /=. 
have hu: inc (J i i) (diagonal I) by rewrite {2} ea.
by move/setXb_P: tp => [_ _ px]; rewrite LgV// idV//;aw; apply: px; rewrite dE.
Qed.
End Example1.

Definition right_directed_on r I :=
  forall x y, inc x I -> inc y I ->
              exists z, [/\ inc z I, gle r x z & gle r y z]. 

Section Example2.
Variables I r F: Set.
Hypotheses (or:preorder r) (sr: substrate r = I) (rdr:right_directed_on r I).

Definition prl_exa2_system: projective_system.
Proof.
apply: (@ProjectiveSystem (cst_graph I F) I r (cst_graph r (identity F))).
- by [].
- by [].
- by fprops.
- by aw.
- by fprops.
- by aw.
- move => i ir; move:(pr1_sr ir)(pr2_sr ir); rewrite sr=> i1 i2.
  rewrite ! LgV//; exact: identity_prop.
- move => i j k ha hb; rewrite !LgV//; aw; first exact: compf_id_id. 
  by move:or => [_  _ tr]; apply:(tr _ _ _ ha hb).
- by move:or => [_ tr _]; move => i iI; rewrite !LgV//; apply: tr; rewrite sr.
Defined.

Lemma prl_exa2_prop: 
  projective_system_on prl_exa2_system
  (cst_graph I F) I r (cst_graph r (identity F)).
Proof.  by []. Qed.


Lemma prl_exa2_prop2: projective_limit prl_exa2_system = diagonal_graphp F I. 
Proof.
have pa: domain (psE prl_exa2_system) = I by simpl; aw.
set_extens t.
  move/prl_limitP => [qa qb qc hb]; apply /diagonal_graph_P. 
  rewrite qb; split => //.
    split => // i j; rewrite qb /= => iI jI.
    move:(rdr  iI jI) => [k [_ km2 kl2]].
    rewrite (hb _ _ km2) (hb _ _ kl2).
    by rewrite (cst_graph_ev _ km2) (cst_graph_ev _ kl2).
  move => s /(range_gP qa)  [u ud ->]; rewrite qb in ud.
  by move: (qc _ ud); rewrite LgV// - pa.
move => /diagonal_graph_P [[ha hb] hc hd]; apply /prl_limitP; split => //.
  by move => i ide /=; rewrite LgV//; apply/ hd /(range_gP ha); exists i => //; rewrite hc.
move => i j lea1.
have idr: inc i (substrate r) by order_tac.
have idt: inc i (domain t) by rewrite hc - sr.
have jdr: inc j (substrate r) by order_tac.
have jdt: inc j (domain t) by rewrite hc - sr.
have hae:inc (Vg t j) F by apply/ hd /(range_gP ha); exists j.
rewrite !LgV// idV//; exact:(hb _ _  idt jdt).
Qed.

End Example2.


Section Example3.
Let r := Nat_order.
Let f := fun i j => Lf (fun x => x +c (j -c i)) Nat Nat.
Let ffam := Lg r (fun p => f (P p) (Q p)).
Let Efam:= Lg Nat  (fun i => Nat).

Lemma prl_exa3_prop1:
  [/\ preorder r, substrate r = Nat &
      forall i j, gle r i j <-> [/\ natp i, natp j & i <=c j]].
Proof.
move:Nat_order_wor => [[/order_preorder ha _] hb]; split => //.
exact:Nat_order_leP.
Qed.


Lemma prl_exa3_prop2 p: inc p r ->
  [/\ natp (P p), natp (Q p) & gle r (P p) (Q p)].
Proof.
move: prl_exa3_prop1 => [ha hb hc] pr.
move: (proj31 ha _ pr) => pp; rewrite - pp in pr.
by move/hc: (pr) => [hd he _].
Qed.

Lemma prl_exa3_prop3 i j: gle r i j -> lf_axiom (csum2^~ (j -c i)) Nat Nat.
Proof.
move => leij; move/(proj33 prl_exa3_prop1):leij => [ha hb hc] => x xN.
exact: (NS_sum xN (NS_diff _ hb)).
Qed.

Lemma prl_exa3_prop4 i j: gle r i j -> function_prop (f i j) Nat Nat.
Proof.
rewrite/f;saw; apply: lf_function.
by apply: prl_exa3_prop3.
Qed.
  
Definition prl_exa3_system: projective_system.
Proof.
apply: (@ProjectiveSystem Efam Nat r ffam).
- exact (proj31 prl_exa3_prop1).
- exact (proj32 prl_exa3_prop1).
- rewrite /Efam; fprops.
- by rewrite /Efam;aw.
- rewrite /ffam; fprops.
- by rewrite /ffam; aw.
- move => i ir; move:(prl_exa3_prop2 ir)=> [ha hb hc].
  by rewrite /Efam /ffam !LgV//; apply: prl_exa3_prop4.
- move => i j k leij lejk; rewrite /ffam.
  move:(proj33 (proj31 prl_exa3_prop1) _ _ _ leij lejk) => leik.
  move:(prl_exa3_prop4 leij)=> [fij sij tij].
  move:(prl_exa3_prop4 leik)=> [fik sik tik].
  move:(prl_exa3_prop4 lejk)=> [fjk sjk tjk].
  have cop:f i j \coP f j k by split => //; ue.
  rewrite !LgV//; aw; apply: function_exten.
  + fct_tac.
  + exact.
  + by rewrite compf_s sik.
  + by rewrite compf_t tij.
  + rewrite compf_s sjk => n nN; rewrite compfV //; last by ue.
    move:(prl_exa3_prop3 leij)(prl_exa3_prop3 leik)(prl_exa3_prop3 lejk).
    move => axij axik axjk.
    rewrite /f !LfV//; last by aw; apply: axjk.
    move/(proj33 prl_exa3_prop1): leij => [iN jN lij].
    move/(proj33 prl_exa3_prop1): lejk => [_ kN ljk].
    rewrite - csumA - cdiff_pr4 // (csumC j i) cdiff_pr5 //; fprops.
- move => i iN.
  have ha: inc (J i i) r.
    by move:(prl_exa3_prop1) => [/proj32 hu hv _];apply: hu; rewrite hv.
  move: (prl_exa3_prop4 ha) => ff.
  rewrite /ffam/Efam ! LgV//; aw; apply: (identity_prop0 ff) => x xN.
  rewrite /f LfV//; last by apply:prl_exa3_prop3.
  rewrite cdiff_nn csum0r; fprops.
Defined.

Lemma prl_exa3_prop5: projective_system_on prl_exa3_system Efam Nat r ffam.
Proof. by []. Qed.

Lemma prl_exa3_prop6 x: inc x (projective_limit  prl_exa3_system) ->
   (natp (Vg x \0c) /\ forall i, natp i -> Vg x \0c = (Vg x i) +c i).
Proof.
move=> /prl_limitP /= [ha hb hc hd].
have ns0 := NS0.
have rd: inc (Vg x \0c) Nat by move:(hc _ NS0); rewrite /Efam LgV.
split => // i iN.
have le1: gle r \0c i.
  by apply/(proj33  prl_exa3_prop1);split; fprops; apply:cle0n.
have ra: inc (Vg x i) Nat by  move:(hc _ iN); rewrite /Efam LgV.
have rb:= (prl_exa3_prop3 le1).
move:(hd _ _ le1); rewrite /ffam /f LgV// LfV//; aw;trivial.
rewrite (cdiff_n0  iN).
move:(hd _ _ le1); rewrite /ffam /f LgV//. 
Qed.

Lemma prl_exa3_prop7: projective_limit prl_exa3_system = emptyset.
Proof.
apply/set0_P => t /prl_exa3_prop6 [ha hb].
move:(hb _ (NS_succ ha)); set x := Vg _ _; set y :=  Vg _ _ => eqa.
move:(csum_Mle0 y (CS_succ x)); rewrite - eqa => le1.
by move:(cltNge (cltS ha) le1).
Qed.

End Example3.


Definition prl_restr S J (H: sub J (psI S)) : projective_system.
Proof.
apply(@ProjectiveSystem   (restr (psE S) J) J (induced_order (psr S) J)
           (restr (psf S) (induced_order (psr S) J))).
- by apply:(iorder_preorder _ (ps_preorder_r S)); rewrite ps_substrate_r.
- have ha: (sub J (substrate (psr S))) by  rewrite ps_substrate_r.
  exact: ipreorder_sr (ps_preorder_r S) ha.
- fprops.
- by aw.  
- fprops.
- by aw.
- move => i ii; move/setI2_P: (ii) => [iI /setX_P [sa sb sc]]; rewrite !LgV //.
  by apply: ps_function_f.
- move => i j k sa sb.
  move/iorder_gleP: (sa) => [iK jK le1].
  move/iorder_gleP: (sb) => [_ kK le2]. 
  have sc:inc (Pair.J i k) (induced_order (psr S) J).
    apply/iorder_gleP; split => //.
    by apply:(proj33 (ps_preorder_r S) _ _ _ le1 le2).
  by rewrite !LgV//; apply: ps_compose_f.
- move => i ik; rewrite !LgV//; first by apply:ps_identity_f; apply:H.
  apply/iorder_gleP; split => //; apply (proj32 (ps_preorder_r S)).
  by rewrite ps_substrate_r; apply:H.
Defined.


Lemma prl_restr_prop S J (H: sub J (psI S)):
  projective_system_on (prl_restr H)
         (restr (psE S) J) J (induced_order (psr S) J)
         (restr (psf S) (induced_order (psr S) J)).
Proof. done. Qed.


Lemma prl_restr_Iv2 S S' J (h1: sub J (psI S))(h2: sub J (psI S')):
  prl_same_data S S' -> 
  prl_same_data (prl_restr h1) (prl_restr h2). 
Proof.
move => [ea eb ec].
move:(prl_restr_prop h1) => [pa pb pc pd].
move:(prl_restr_prop h2) => [pa' pb' pc' pd'].
by rewrite /prl_same_data pa pc pd pa' pc' pd' ea eb ec.
Qed.

Definition projective_limit_restr S J (H: sub J (psI S)):=
  projective_limit (prl_restr H).


Definition prl_restr_canonical S J (H: sub J (psI S)):=
  Lf (restr^~J) (projective_limit S) (projective_limit_restr H).

Lemma prl_restr_canonical_ax S J (H: sub J (psI S)) :
  lf_axiom (restr^~J) (projective_limit S) (projective_limit_restr H).
Proof.
move =>  x /Zo_P [hc hd].
apply /prl_limitP;split; aw; fprops.
  move => i /= iK; rewrite !LgV//; move/setXb_P: hc => [_ _]; apply.
  by rewrite ps_domain_E; apply:H. 
move => i j /= ra.
by move/setI2_P: (ra) => [rb /setXp_P [iK jK]]; rewrite !LgV//; apply:hd.
Qed.

Lemma prl_restr_canonical_fp S J (H: sub J (psI S)):
 function_prop (prl_restr_canonical H) (projective_limit S)
               (projective_limit_restr H).
Proof.
rewrite /prl_restr_canonical; saw.
apply:(lf_function (prl_restr_canonical_ax H)).
Qed.

Lemma prl_restr_canonical_fun_ev S J (H: sub J (psI S)) x:
 inc x (projective_limit S) -> Vf (prl_restr_canonical H)  x = restr x J.
Proof.
move => xs; rewrite /prl_restr_canonical LfV//.
apply: (prl_restr_canonical_ax H).
Qed.

Lemma prl_restr_canonical_fun_ev2 S J (H: sub J (psI S)) x j:
  inc x (projective_limit S) -> inc j J ->
  Vg (Vf (prl_restr_canonical H) x) j = Vg x j.
Proof.
move => xs iJ;rewrite (prl_restr_canonical_fun_ev H xs); rewrite LgV//.
Qed.

Lemma projective_limit_restr_double_Iv S K K'
  (H1:sub K (psI S)) (H2: sub K' K):
  prl_same_data (prl_restr (H2: sub K' (psI (prl_restr H1))))
    (prl_restr (sub_trans H2 H1)).
Proof.
have ha: restr (restr (psE S) K) K' = restr (psE S) K'.
  by rewrite double_restr.
have hb: induced_order (induced_order (psr S) K) K' = induced_order (psr S) K'.
  by rewrite (iorder_trans _ H2).
split => //=;rewrite double_restr ? hb // => t /setI2_P [qa qb].
by apply/setI2_P; split => //; apply: (setX_Sll H2).
Qed.


Lemma projective_limit_restr_double S K K'
  (H1:sub K (psI S)) (H2: sub K' K):
  projective_limit_restr (H2: sub K' (psI (prl_restr H1))) =
   projective_limit_restr (sub_trans H2 H1).
Proof.
apply: projective_limit_Iv;apply:projective_limit_restr_double_Iv.
Qed.

Lemma prl_restr_canonical_comp S K K'
      (H1:sub K (psI S)) (H2: sub K' K)
      (g :=  prl_restr_canonical H1) 
      (g' :=  prl_restr_canonical (H2: sub K' (psI (prl_restr H1))))
      (g'' :=  prl_restr_canonical (sub_trans H2 H1)):
   g' \coP  g /\ g' \co g = g''.
Proof.
case: (prl_restr_canonical_fp H1) => [pa pb pc].
case: (prl_restr_canonical_fp (sub_trans H2 H1))=> [pa'' pb'' pc''].
case:(prl_restr_canonical_fp (H2: sub K' (psI (prl_restr H1))))=> [pa' pb' pc'].
have hu: g' \coP g by hnf; rewrite pc pb'. 
split => //; apply: (function_exten (compf_f hu) pa''); aw.
- by rewrite pb pb''.
- by rewrite pc'' pc' (projective_limit_restr_double H1 H2).
- move => t tg /=; move:(tg); rewrite pb => tg'.
  rewrite /g/g' compfV // !prl_restr_canonical_fun_ev //.
    by rewrite double_restr.   
  exact: (prl_restr_canonical_ax H1).
Qed.

(** Inverse systems of mappings *)



Definition prl_map_compat S u F:=
  [/\ fgraph u, domain u = psI S, 
   forall i, inc i (domain u) -> function_prop (Vg u i) F (Vg (psE S) i) &
   forall i j, gle (psr S) i j -> Vg (psf S) (J i j) \co (Vg u j) = Vg u i].

Definition prl_map_property S u F g:=
  function_prop g F (projective_limit S) /\
  forall i, inc i (domain u) -> (Vg u i) = (prl_can_fun S i) \co g.

Definition prl_map_val S u :=
  fun y => Lg (psI S) (fun i => Vf (Vg u i) y).

Definition projective_map S u F :=
  Lf (prl_map_val S u) F (projective_limit S).

Lemma prl_map_property_res1 S u F g i x:
  prl_map_compat S u F -> prl_map_property S u F g ->
  inc i (psI S) -> inc x F -> Vf (Vg u i) x = Vg (Vf g x) i.
Proof.
move => [p1 p2 p3 p4] [[fg sg tg] hb] iI xp.
rewrite p2 in hb; rewrite (hb _ iI).
have xsg: inc x (source g) by rewrite sg.
have vxt: inc (Vf g x) (projective_limit S) by Wtac.
move:(prl_can_fun_fp iI) => [fi si ti].
have cop: prl_can_fun S i \coP g by split => //; ue.
by rewrite compfV //(prl_proj_ev iI vxt).
Qed.


Lemma prl_map_unique S u F g g':
  prl_map_compat S u F ->
  prl_map_property S u F g -> prl_map_property S u F g' ->
  g = g'.
Proof.
move => hb cp1 cp2; move:(cp1)(cp2)=>[[fg sg tg] gp] [[fg' sg' tg'] gp'].
apply: function_exten => //; try ue; move => i isg /=.
have isg': inc i (source g') by rewrite sg' - sg. 
have hu: inc (Vf g i) (projective_limit S) by rewrite - tg; fprops.
have hu': inc (Vf g' i) (projective_limit S) by rewrite  - tg'; fprops.
move/prl_limitP:(hu) => [hc hd he hf].
move/prl_limitP:(hu') => [hc' hd' he' hf'].
apply:fgraph_exten => //; rewrite hd ? hd' => // j jde.
have iif: inc i F by ue.
rewrite -(prl_map_property_res1 hb cp1 jde iif).
by rewrite -(prl_map_property_res1 hb cp2 jde iif).
Qed.


Lemma prl_map_ax S u F :
  prl_map_compat S u F ->
  lf_axiom (prl_map_val S u ) F (projective_limit S).
Proof.
move => [cp1 cp2 cp3 cp4] y yF.
rewrite cp2 in cp3.
rewrite /prl_map_val;apply/prl_limitP;aw;split; fprops.
  move => i iI. 
  move: (cp3 i iI) => [fui sui tui].
  by rewrite !LgV//  - tui; apply: (Vf_target fui); rewrite sui.
move => i j lij; rewrite /prl_map_val /=.
move:(prl_prop0 lij) => [isr jsr].
move: (cp3 _ jsr) =>  [fuj suj tuj].
have ysr: inc y (source (Vg u j)) by rewrite suj.
have cop: Vg (psf S) (J i j) \coP Vg u j.
  move:(ps_function_f  lij) => [ff sf tf].
  by split => //; rewrite sf tuj pr2_pair.
rewrite !LgV//; move/(f_equal (fun z => (Vf z y))):(cp4 _ _ lij).
by rewrite compfV.
Qed.

Lemma projective_map_ev S u F x i:
  prl_map_compat S u F -> inc x F -> inc i (psI S) ->
  Vg (Vf (projective_map S u F) x) i = Vf (Vg u i) x.
Proof.
move => /prl_map_ax ax xF iI.
rewrite /projective_map /prl_map_val LfV// LgV//.
Qed.


Lemma prl_map_prop S u F :
  prl_map_compat S u F ->
  prl_map_property S u F (projective_map S u F).
Proof.
move => hb.
move:(prl_map_ax hb) => hc.
set g := (projective_map S u F).
have fg: function g by apply:lf_function.
have sg: source g = F by rewrite /g/projective_map; aw.
have tg: target g = (projective_limit S) by rewrite /g/projective_map; aw.
have gp:inc g (functions F (projective_limit S)) by apply/functionsP.
move: hb => [hb1 hb2 hb3 hb4].
split => // i idu.
move: (hb3 _ idu) => [fui sui tui].
have ide:inc i (psI S) by rewrite - hb2.
move: (prl_can_fun_fp ide) => [fp sp tp].
have cop:prl_can_fun S i \coP g by split => //; ue.
apply:function_exten;[ done | by apply: compf_f | by aw; rewrite sg | | ].
  by aw; rewrite tp.
rewrite sui; move => j jsu /=.
have jsg: inc j (source g) by rewrite sg.
have aux: inc (Vf g j) (projective_limit S) by Wtac.
rewrite compfV //prl_proj_ev // projective_map_ev //. 
Qed.


Lemma prl_map_inj S u F :
  prl_map_compat S u F ->
  (injection (projective_map S u F) <->
   (forall y z, inc y F -> inc z F -> y <> z
           -> exists2 i, inc i (psI S) & (Vf (Vg u i) y <> Vf (Vg u i) z))). 
Proof.
move => hb.
move:(prl_map_prop hb) => [[fg sg tg]].
move: (prl_map_ax  hb) => hu.
split.
  move => [hc hd] y z yF zF yz; ex_middle bad; case:yz.
  rewrite sg in hd; apply: (hd y z yF zF); rewrite /projective_map/prl_map_val.
  rewrite !LfV//; apply: Lg_exten => i iS; ex_middle bad2; case: bad; ex_tac.
move => h; split => //; rewrite sg => y z yF zF eq.
case: (equal_or_not y z) => eyz//.
move: (h _ _ yF zF eyz) => [i id]; case.
move/(f_equal (Vg^~i)):eq.
rewrite (projective_map_ev hb yF id).
by rewrite (projective_map_ev hb zF id). 
Qed.

Definition prl_map2_compat S S' u:=
  [/\ fgraph u, domain u = psI S, 
   forall i, inc i (psI S) ->
             function_prop (Vg u i) (Vg (psE S) i) (Vg (psE S') i) &
   forall i j, gle (psr S) i j -> (Vg u i) \co (Vg (psf S) (J i j)) =
         (Vg (psf S') (J i j)) \co (Vg u j)].

Definition prl_map2_property S S' u g:=
  function_prop g  (projective_limit S) (projective_limit S')
  /\ forall i, inc i (psI S) -> 
   (Vg u i) \co (prl_can_fun S i) =
          (prl_can_fun S') i \co g.

Definition prl_map2_aux S u := 
  Lg (psI S) (fun i => (Vg u i) \co (prl_can_fun S i)).

  
Lemma prl_map2_prop1 S S' u: 
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  prl_map_compat S' (prl_map2_aux S u) (projective_limit S).
Proof.
move => pa [pd pe pf pg]. 
have ha:= (prl_same_index_same_I pa).
rewrite /prl_map2_aux; split; aww.
  move => i iI; rewrite LgV//.
  move:(pf _ iI) => [fui sui tui].
  move:(prl_can_fun_fp iI) => [fp sp tp].
  by saw; fct_tac; rewrite sui.
move => i j le1.
have le2: gle (psr S) i j by rewrite pa.
move: (prl_prop0 le2) => [isr jsr].
move : (pf _ isr) => [fui sui tui].
move : (pf _ jsr) => [fuj suj tuj].
move: (ps_function_f  le2) =>  [fa sfa tga].
move: (ps_function_f le1) =>  [fa' sfa' tga'].
have cp1: Vg (psf S') (J i j) \coP Vg u j.
  by split => //; rewrite sfa' tuj; aw.
rewrite - pa in le1;move:(prl_can_fun_fp jsr) => [ ha' hb hc].
have cp2:Vg u j \coP prl_can_fun S j.
  by split => //; rewrite hc.
have cp3: Vg u i \coP Vg (psf S) (J i j).
  by split => //; rewrite tga sui; aw.
move: (prl_can_fun_prop le1) => [hd he].
by rewrite !LgV// compfA // - (pg _ _ le1) - compfA // - he.
Qed.

  
Lemma prl_map2_prop2 S  u i t:
  inc i (psI S) -> inc t (projective_limit S) ->
  function (Vg u i) -> source (Vg u i) = Vg (psE S) i ->
  Vf (Vg (prl_map2_aux S u) i) t = Vf (Vg u i) (Vg t i).
Proof.
move => iI tlim  fu su.
move:  (prl_can_fun_fp iI) => [ff sf tf].
have tl: inc t (source (prl_can_fun S i)) by ue.
have hh: Vg u i \coP prl_can_fun S i.
  by split => //;  rewrite tf.
by rewrite /prl_map2_aux LgV// compfV// prl_proj_ev.
Qed.

Lemma prl_map2_unique S S' u g g':
  prl_same_index S S' -> prl_map2_compat S S' u->
  prl_map2_property S S' u g -> prl_map2_property S S' u  g' -> g = g'.
Proof.
move => ha hb.
move: (prl_map2_prop1 ha hb); rewrite /prl_map2_aux; set v := Lg _ _ =>  he.
move => [g1 g2] [g3 g4].
have dv: domain v = psI S by rewrite /v; aw.
have hu1: prl_map_property S' v (projective_limit S) g.
  split => //. rewrite dv=> i idv; rewrite - g2 //; rewrite /v LgV//.
have hu2: prl_map_property S' v (projective_limit S) g'.
  split => //; rewrite dv=> i idv; rewrite - g4 //; rewrite /v LgV//.
exact:(prl_map_unique  he hu1 hu2).
Qed.

Definition projective_limit_fun S S' u :=
   projective_map S' (prl_map2_aux S u) (projective_limit S).

Lemma prl_map2_prop S S' u (g := projective_limit_fun S S' u):
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  prl_map2_property S S' u g.
Proof.
move => ha hb.
move:(prl_map2_prop1 ha hb); set v :=  (prl_map2_aux S u) => hc.
move: (prl_map_prop hc); rewrite /v -/(projective_limit_fun _ _ _) -/g.
move => [qa qb].
split => // i iI.
have idx: inc i (domain (prl_map2_aux S u)) by rewrite /prl_map2_aux; aw.
by rewrite - qb // /prl_map2_aux LgV.
Qed.

Lemma prl_projective_limit_fun_IV2 S1 S2 x S1' S2' x':
  prl_same_data S1 S1' ->  prl_same_data S2 S2' -> x = x' ->
  projective_limit_fun S1 S2 x = projective_limit_fun S1' S2' x'.
Proof.
move => ha hb hc.
rewrite /projective_limit_fun -hc -(projective_limit_Iv ha).
have <-: (prl_map2_aux S1 x) = (prl_map2_aux S1' x).
  have si: (psI S1) =  (psI S1').
    by rewrite -!ps_substrate_r; case: ha => _ -> _.
   rewrite /prl_map2_aux - si; apply: Lg_exten => i ii.
   by rewrite (prl_can_fun_Iv i ha ).
have si: (psI S2) =  (psI S2')  by rewrite -!ps_substrate_r; case: hb => _ -> _.
by rewrite /projective_map -(projective_limit_Iv hb) /prl_map_val si.
Qed.


Lemma prl_map2_compat_aux S S' u x i j:
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  inc x (projective_limit S) -> gle (psr S) i j ->
  Vf (Vg u i) (Vg x i) = Vf (Vg (psf S') (J i j)) (Vf (Vg u j) (Vg x j)).
Proof.
move => ha [hb1 hb2 hb3 hb4]  /prl_limitP [fgx dx xv xw] lij.
move: (prl_prop0 lij) => [iI jI].
have lij':  gle (psr S') i j by rewrite - ha.
move: (hb3 _ iI) => [fui sui tui].
move: (hb3 _ jI) => [fuj suj tuj].
move: (ps_function_f lij) => [fij sij tij].
move: (ps_function_f lij') => [fij' sij' tij'].
have co1: Vg u i \coP Vg (psf S) (J i j) by split => //; rewrite sui tij; aw.
have co2: Vg (psf S') (J i j) \coP Vg u j by split => //; rewrite sij' tuj;aw.
have xs1:  inc (Vg x j) (source (Vg u j))  by rewrite suj; apply: xv.
have xs2:  inc (Vg x j) (source (Vg (psf S) (J i j))).
  by rewrite sij pr2_pair;apply: xv.
move: (f_equal (Vf ^~(Vg x j)) (hb4 _ _ lij)).
by rewrite !compfV//; move <-; rewrite - (xw _ _ lij).
Qed.

Lemma prl_map_val_aux2 S S' u  (Ha :prl_same_index S S')
      (Hu: prl_map2_compat S S' u)
      (f := projective_limit_fun S S' u) i x:
   inc i (psI S) ->  inc x (projective_limit S) ->
   (Vf (Vg u i) (Vg x i)) = (Vg (Vf f x) i).
Proof.
move => iI xs.
move: (Hu) => [hu1 hu2 hu3 hu4].
move: (hu3 _ iI) => [fu su tu].
move: (prl_map2_prop Ha Hu) => [[ff sf tf] fp].
have iI': inc i (psI S') by rewrite  -(prl_same_index_same_I Ha).
move:(prl_proj_ax iI)(prl_proj_ax iI') => ax1  ax2.
have xs2: inc x (source (projective_limit_fun S S' u)) by ue.
have xs1: inc (Vg x i) (source (Vg u i)) by move:(ax1 _ xs); rewrite su.
have xp1:inc (Vf (projective_limit_fun S S' u) x) (projective_limit S') by Wtac.
move:(prl_can_fun_fp iI) => [fi si ti].
move:(prl_can_fun_fp iI') => [fi' si' ti'].
have xs3: inc x (source (prl_can_fun S i)) by rewrite si.
have co1:Vg u i \coP prl_can_fun S i  by split => //; ue.
move: (f_equal (Vf ^~x) (fp _ iI)).
rewrite /prl_can_fun compfV // LfV //  compfV //; first rewrite LfV //.
split => //; ue.
Qed.

Lemma prl_map2_compose S S' S'' u v (F := projective_limit_fun)
  (w:= Lg (psI S) (fun i => (Vg v i) \co (Vg u i))) :
  prl_same_index S S' ->  prl_same_index S' S'' ->
  prl_map2_compat S S' u -> prl_map2_compat S' S'' v ->
  prl_map2_compat S S'' w /\
  F S S'' w = F S' S'' v \co F S S' u.
Proof.
move => sb1 sb2 hu hv.
have sb3: prl_same_index S S'' by  rewrite /prl_same_index sb1.
move:(prl_map2_prop sb1 hu); rewrite -/F => pa1.
move:(prl_map2_prop sb2 hv); rewrite -/F => pa2.
move: hu hv=> [cpa1 cpa2 cpa3 cpa4]  [cpb1 cpb2 cpb3 cpb4]. 
have ssI:= prl_same_index_same_I sb1.
rewrite - ssI in cpb3.
have ha i: inc i (psI S) ->  Vg v i \coP Vg u i.
    move => iI.
    move: (cpa3 _ iI)  (cpb3 _ iI) =>[fu su tu] [fv sv tv].
    by split => //;rewrite sv tu.
have hb i j: gle (psr S) i j -> Vg u i \coP Vg (psf S) (J i j).
  move => lij.
  move:(ps_function_f lij)(prl_prop0 lij) => [ff sf tf] [ /cpa3 [fu su tu] _].
  by split => //; rewrite su tf; aw.
have hb' i j: gle (psr S') i j ->   Vg v i \coP Vg (psf S') (J i j).
  move => lij; move:(lij); rewrite - sb1 => lij'.
  move:(ps_function_f lij) (prl_prop0 lij')=> [ff sf tf] [ /cpb3 [fu su tu] _].
  by split => //; rewrite su tf; aw.
have hc i j:  gle (psr S) i j ->   Vg (psf S') (J i j) \coP Vg u j.
  move => lij;  move:(lij); rewrite sb1 => lij'.
  move:(ps_function_f lij') (prl_prop0 lij)  => [ff sf tf] [_ /cpa3 [fu su tu]].
  by split => //; rewrite sf tu; aw.
have hc' i j: gle (psr S) i j ->  Vg (psf S'') (J i j) \coP Vg v j.
  move => lij; move:(lij); rewrite sb1 sb2 => lij'.
  move: (prl_prop0 lij) (ps_function_f lij') => [_ /cpb3[fu su tu]] [ff sf tf].
  by split => //; rewrite sf tu; aw.
have cpc:prl_map2_compat S S'' w.
  rewrite /w; split; aww.
    move => i iI; rewrite LgV//.
    move:(cpa3 _ iI) (cpb3 _ iI) => [fu su tu] [fv sv tv].
    by saw;fct_tac; rewrite sv tu.
  move => i j lij.
  have lij': gle (psr S') i j by rewrite - sb1.
  move:(prl_prop0 lij)=> [isr jsr]; rewrite !LgV//.
  rewrite - (compfA  (ha _ isr) (hb _ _ lij)) (cpa4 _ _ lij).
  rewrite (compfA (hb' _ _ lij') (hc _ _ lij)) (cpb4 _ _ lij').
  by rewrite (compfA  (hc' _ _ lij) (ha _ jsr)).
split; first exact.
apply:(prl_map2_unique  sb3 cpc (prl_map2_prop sb3 cpc)).
move: pa1  pa2=> [[ff sf tf] ra2] [ [ff' sf' tf'] ra4].
have ra3: F S' S'' v \coP F S S' u by split => //; rewrite sf' tf.
split; first by saw; apply: compf_f.
move => i iI.
have ssI':= prl_same_index_same_I sb3.
have iI': inc i (psI S') by rewrite - ssI. 
have iI'': inc i (psI S'') by rewrite - ssI'. 
move: (prl_can_fun_fp iI'') => [fpl'' spl'' tpl''].
move: (prl_can_fun_fp iI') =>  [fpl' spl' tpl'].
move: (prl_can_fun_fp iI) =>  [fpl spl tpl].
move: (cpb3 _ iI) => [fv sv tv].
move: (cpa3 _ iI) => [fu su tu].
have qa: prl_can_fun S'' i \coP F S' S'' v.
   by split => //; rewrite spl'' tf'.
have qb: Vg v i \coP prl_can_fun S' i by split => //; rewrite sv tpl'.
have qc: prl_can_fun S' i \coP F S S' u.
  by split => //; rewrite spl' tf.
have qd: Vg u i \coP prl_can_fun S i by split => //; rewrite su tpl.
rewrite (compfA qa ra3) - (ra4  _ iI') - (compfA qb qc) - (ra2 _ iI).
rewrite (compfA (ha _ iI) qd)  /w LgV//.
Qed.


Lemma prl_map2_prop3 S S' u  (Ha :prl_same_index S S')
      (Hu: prl_map2_compat S S' u)
      (f := projective_limit_fun S S' u):
  function_prop f (projective_limit S)  (projective_limit S') /\
  forall i x,
   inc i (psI S) ->  inc x (projective_limit S) ->
   (Vf (Vg u i) (Vg x i)) = (Vg (Vf f x) i).
Proof.
have ra:=(proj1 (prl_map2_prop Ha Hu)).
have rb:= (prl_map_val_aux2 Ha Hu).
done.
Qed.  

Definition prl_product_E S S':= 
   Lg (psI S) (fun i => (Vg (psE S) i) \times (Vg (psE S') i)).
Definition prl_product_f S S' := 
  Lg (psr S) (fun i => (Vg (psf S) i) \ftimes (Vg (psf S') i)).

Definition prl_system_product S S' (sd: prl_same_index S S'): projective_system.
Proof.
apply:(@ProjectiveSystem (prl_product_E S S') (psI S) (psr S)
                           (prl_product_f S S')).
- exact:(ps_preorder_r S).
- exact (ps_substrate_r S).
- rewrite /prl_product_E ; fprops.
- by rewrite /prl_product_E ; aw.
- rewrite /prl_product_f ; fprops.
- by rewrite /prl_product_f ; aw.
- move => i ir.
  move:(ir); rewrite sd => ir'.
  have pi:= ((proj31 (ps_preorder_r S)) _ ir).
  move:(ir);rewrite -{1} pi  => /prl_prop0 [pI qI].
  rewrite /prl_product_E /prl_product_f ; rewrite !LgV//.
  exact: (ext_to_prod_fun_bis (ps_function_f ir) (ps_function_f ir')).
- move => i j k lij ljk.
  move:(proj33 (ps_preorder_r S) _ _ _ lij ljk) => lik.
  move:(lij)(ljk); rewrite sd => lij' ljk'.
  rewrite /prl_product_f !LgV//.
  move: (ps_function_f lij)(ps_function_f lij'); aw => ha hb.
  move: (ps_function_f ljk)(ps_function_f ljk'); aw => hc hd.
  rewrite (ext_to_prod_comp_bis hc hd ha  hb) !ps_compose_f //.
- move => i iI.
  have iI': inc i (psI S') by rewrite - (prl_same_index_same_I sd).
  move:(prl_prop1 iI) => iiI.
  rewrite /prl_product_f /prl_product_E !LgV //.
  rewrite !ps_identity_f //; apply:ext_to_prod_identity.
Defined.


Lemma prl_system_product_prop S S' (sd: prl_same_index S S'):
  projective_system_on (prl_system_product sd) 
   (prl_product_E S S') (psI S) (psr S) (prl_product_f S S').
Proof. by []. Qed.

Definition prl_product_can_fun S S' :=
  Lg (psI S) (fun i => (prl_can_fun S i)
                         \ftimes (prl_can_fun S' i)).


Lemma prl_product_can_fun_compat  S S' (sd: prl_same_index S S'):
  prl_map_compat (prl_system_product sd) (prl_product_can_fun S S')
  ((projective_limit S) \times (projective_limit S')).
Proof.
move:(prl_system_product_prop sd) => [ha hb hc hd].
have ssI := prl_same_index_same_I sd.
rewrite /prl_product_can_fun ; split; aww.
   rewrite ha /prl_product_E; move => i iI; rewrite !LgV//.
  by apply:ext_to_prod_fun_bis; apply:prl_can_fun_fp => //; rewrite - ssI.
rewrite hc;move => i j lij; move: (prl_prop0 lij) => [iI jI]; aw.
have jI': inc j (psI S') by rewrite - ssI.
have lij':  gle (psr S') i j by rewrite - sd.
move: (ps_function_f lij) (ps_function_f lij'); aw => h3 h4.
rewrite hd /prl_product_f !LgV//.
rewrite(ext_to_prod_comp_bis (prl_can_fun_fp jI) (prl_can_fun_fp jI') h3 h4).  
by rewrite - (proj2(prl_can_fun_prop lij))  (proj2(prl_can_fun_prop lij')).
Qed.

Lemma prl_product_can_fun_bij  S S' (sd: prl_same_index S S')
  (E:=  projective_limit S) (E' := projective_limit S')
  (f:= projective_map (prl_system_product sd) (prl_product_can_fun S S')
         (E \times E')):
   bijection_prop f
      (E \times E') (projective_limit (prl_system_product sd)).
Proof.
move:(prl_system_product_prop sd) => [pa pb pc pd].
move:(prl_product_can_fun_compat sd) => ha.
move:(prl_map_prop ha) (prl_map_ax ha).
have ssI:= (prl_same_index_same_I sd). 
rewrite -/E -/E' -/f; move =>[hc hd ] he.
rewrite /f/projective_map; saw; apply:lf_bijective.
- exact:he.
-  move => u v ua va.
   move: (ua)=>/setX_P[pu p1u p2u]; move:(va)=> /setX_P[pv p1v p2v].
   rewrite /prl_map_val pb => ww.
   have hh i: inc i (psI  S) ->
              J (Vg (P u) i) (Vg (Q u) i) = J (Vg (P v) i) (Vg (Q v) i).
    move => iI.
    move:(iI); rewrite ssI => iI'.
    move:(prl_can_fun_fp iI) => [ffi sf tf].
    move:(prl_can_fun_fp iI') => [ffi' sf' tf'].
    move:(prl_proj_ax iI)(prl_proj_ax iI') => ax ax'.
    move:(f_equal (Vg ^~i) ww);rewrite /prl_product_can_fun !LgV//.
    rewrite ext_to_prod_V2 // ? ext_to_prod_V2 //. 
    + rewrite /prl_can_fun !LfV//.
    + by rewrite sf sf'.
    + by rewrite sf sf'.
  move/prl_limitP:p1u => [ha1 hb1 hc1 hd1].
  move/prl_limitP:p2u => [ha2 hb2 hc2 hd2].
  move/prl_limitP:p1v => [ha3 hb3 hc3 hd3].
  move/prl_limitP:p2v => [ha4 hb4 hc4 hd4].
  apply: pair_exten => //; apply: fgraph_exten => //. 
  + by rewrite hb1 hb3.
  + rewrite hb1;move => i iI; exact: (pr1_def (hh _ iI)).
  + by rewrite hb2 hb4.
  + rewrite hb2 - ssI => i iI; exact: (pr2_def (hh _ iI)).
move => y yi.
move /Zo_P: yi => [/setXb_P []].
rewrite pa pc pd /prl_product_E; aw => fgy dy yv yw.
set x1 := Lg (psI S) (fun i => P (Vg y i)).
set x2 := Lg (psI S) (fun i => Q (Vg y i)).
have yv1 i: inc i (psI S) ->
  [/\ pairp (Vg y i), inc (P (Vg y i)) (Vg (psE S) i)
                                     & inc (Q (Vg y i)) (Vg (psE S') i)].
   by move => iI; move:(yv _ iI); rewrite LgV//; case/setX_P.
have x1p:inc x1 (projective_limit S).
  rewrite /x1;apply/Zo_P; split.
     apply/setXb_P;split; fprops;rewrite ps_domain_E; aw; trivial.
     by move => i iI; rewrite !LgV//; case: (yv1 _ iI).
  move => i j lij.
  move: (prl_prop0 lij) => [iI jI].
  move:(ps_function_f lij) => [ff sf tf].
  move: (yw _ _ lij); rewrite /prl_product_f ! LgV//.
  rewrite sd in lij; move:(ps_function_f lij) => [ff' sf' tf'].
  rewrite (ext_to_prod_V2 ff ff'); first by move => ->; rewrite pr1_pair. 
  by rewrite sf sf';move: (yv _ jI); rewrite LgV//; aw.
have x2p:inc x2 (projective_limit S').
  rewrite /x2;apply/Zo_P; split.
     apply/setXb_P;split; fprops;rewrite ps_domain_E ssI; aw; trivial.
     by move => i iI; rewrite ! LgV//; rewrite  - ssI in iI;case: (yv1 _ iI).
  move => i j lij.
  move:(ps_function_f lij) => [ff' sf' tf'].
  rewrite - sd in lij;move: (prl_prop0 lij) => [iI jI].
  move: (yw _ _ lij); rewrite /prl_product_f !LgV//.
  move:(ps_function_f lij) => [ff sf tf].
  rewrite (ext_to_prod_V2 ff ff'); first by move => ->; rewrite pr2_pair. 
  by rewrite sf sf';move: (yv _ jI); rewrite LgV//; aw.
set x:= (J x1 x2); exists x; first by apply: setXp_i.
rewrite /prl_map_val /x pb.
apply:fgraph_exten => //; aww.
rewrite dy; move => i iI /=; rewrite LgV//.
move:(prl_can_fun_fp iI) => [ffi sf tf].
move: (iI); rewrite  ssI  => iI'.
move:(prl_can_fun_fp iI') => [ffi' sf' tf'].
move: (prl_proj_ax  iI)(prl_proj_ax  iI') => ax ax'.
rewrite /prl_product_can_fun LgV//; rewrite ext_to_prod_V2 //.
  rewrite /prl_can_fun -(proj31 (yv1 _ iI)) /x /x1 /x2.
  rewrite pr1_pair pr2_pair ! LfV// !LgV//.
by rewrite sf sf'; apply: setXp_i.
Qed.



(* -- subsets of Ei *)
  
Definition prl_subfam_hyp S M:=
  [/\ fgraph M, domain M = psI S,
   forall i, inc i (psI S) -> sub (Vg M i) (Vg (psE S) i) &
   forall i j, gle (psr S) i j -> 
     sub (Vfs (Vg (psf S) (J i j)) (Vg M j)) (Vg M i) ].

Definition prl_subfam_fct S M :=
  Lg  (psr S) (fun z => restriction2 (Vg (psf S) z) (Vg M (Q z)) (Vg M (P z))).

Lemma prl_subfam_prop1 S M (g := prl_subfam_fct S M):
  prl_subfam_hyp S M ->
  [/\ 
   forall z, inc z (psr S) -> 
      restriction2_axioms (Vg (psf S) z) (Vg M (Q z)) (Vg M (P z)),
   forall i j x, gle (psr S) i j -> inc x (Vg M j) ->
     Vf (Vg g (J i j)) x = Vf (Vg (psf S) (J i j)) x,
   forall i, inc i (psr S)-> function_prop (Vg g i) (Vg M (Q i)) (Vg M (P i)),
   forall i j k, gle (psr S) i j -> gle (psr S) j k ->
                 Vg g (J i j) \co  Vg g (J j k) = Vg g (J i k) &
   forall i, inc i (psI S) -> Vg g (J i i) = identity (Vg M i)].
Proof.
move =>[pa pb pc pd].
have rc z: inc z (psr S) ->
       restriction2_axioms (Vg (psf S) z) (Vg M (Q z)) (Vg M (P z)).
  move => zr.
  move:(ps_function_f zr) =>[ff sf tf].
  move: (pr1_sr zr)(pr2_sr zr); rewrite ps_substrate_r => iI jI.
  split.
  - done.
  - by rewrite sf; apply: pc.
  - by rewrite tf; apply: pc.
  - have pz:= ((proj31 (ps_preorder_r S)) _ zr).
    by rewrite -{1} pz;apply: pd; rewrite/ gle/related pz.
have rd:forall i j x, gle (psr S) i j -> inc x (Vg M j) ->
     Vf (Vg g (J i j)) x = Vf (Vg (psf S) (J i j)) x.
  move => i j x ha hb.
  have hb':inc x (Vg M (Q (J i j))) by aw.
  rewrite -(restriction2_V (rc _ ha) hb'); rewrite /g/prl_subfam_fct LgV//.
have re i: inc i (psr S) -> function_prop (Vg g i) (Vg M (Q i)) (Vg M (P i)).
  move => ir; rewrite /g/prl_subfam_fct LgV//.
  exact: (restriction2_prop (rc _ ir)).
have rg i: inc i (psI S) -> Vg g (J i i) = identity (Vg M i).
  move => ii.
  have iiI:= (prl_prop1 ii).
  move:(re _ iiI); aw => fp; apply: (identity_prop0 fp) => x xM.
  by rewrite (rd _ _  _ iiI xM)  (ps_identity_f ii) LfV//; apply: pc.
split => // i j k lij ljk.
have lik: gle (psr S) i k by apply: (proj33 (ps_preorder_r S)) lij ljk. 
move: (re _ lij) => [fij sij tij].
move: (re _ ljk) => [fjk sjk tjk].
move: (re _ lik) => [fik sik tik].
rewrite ! pr1_pair in tij tik tjk.
rewrite ! pr2_pair in sij sik sjk.
have co1:  Vg g (J i j) \coP Vg g (J j k) by  split => //; rewrite sij tjk.
have fc1: function (Vg g (J i j) \co Vg g (J j k)) by apply: compf_f.
apply: function_exten => //.
- by aw; rewrite sik sjk.
- by aw; rewrite tij tik.
aw; rewrite sjk => x xM.
have cpp: Vg (psf S) (J i j) \coP Vg (psf S) (J j k). 
  move: (ps_function_f lij) => [fa fb fc].
  move: (ps_function_f ljk) => [fa' fb' fc'].
  by split => //; rewrite fb fc'; aw.
have vm: inc (Vf (Vg g (J j k)) x) (Vg M j).
  by rewrite - tjk; apply:(Vf_target fjk); rewrite sjk.
have xM': inc x (source (Vg (psf S) (J j k))). 
  move: (ps_function_f ljk) => [_ -> _]; aw; apply:pc => //. 
  rewrite - (ps_substrate_r); order_tac.
have xM'':  inc x (source (Vg g (J j k))) by rewrite sjk.
rewrite (rd _ _ _ lik xM) - (ps_compose_f lij ljk).
by rewrite !compfV //(rd _ _ _ lij vm) (rd _ _ _ ljk xM). 
Qed.

Definition projective_system_subsets
           S M (H:prl_subfam_hyp S M) : projective_system.
Proof.
apply:(@ProjectiveSystem M (psI S) (psr S) (prl_subfam_fct S M)).
- exact: ps_preorder_r.
- by rewrite ps_substrate_r.
- by case:H.
- by case:H.
- by rewrite /prl_subfam_fct; fprops.
- by rewrite /prl_subfam_fct; aw.
- by case: (prl_subfam_prop1 H).
- by case: (prl_subfam_prop1 H).
- by case: (prl_subfam_prop1 H).
Defined.

Lemma prl_subsets_prop S  M (H:prl_subfam_hyp S M) :
  projective_system_on (projective_system_subsets H)
     M  (psI S)  (psr S) (prl_subfam_fct S M).
Proof.  done. Qed.

Lemma prl_subsets_prop_Iv S M
      (H:prl_subfam_hyp S M) (H':prl_subfam_hyp S M) :
  prl_same_data (projective_system_subsets H) (projective_system_subsets H').
Proof.
move:(prl_subsets_prop H) => [ra rb rc rd].
move:(prl_subsets_prop H') => [ra' rb' rc' rd'].
by rewrite /prl_same_data ra rc rd.
Qed.

Lemma prl_subsets_prop_I2v S S' M
      (H:prl_subfam_hyp S M) (H':prl_subfam_hyp S' M) :
  prl_same_data S S' ->
  prl_same_data (projective_system_subsets H) (projective_system_subsets H').
Proof.
move:(prl_subsets_prop H) => [ra rb rc rd].
move:(prl_subsets_prop H') => [ra' rb' rc' rd'].
rewrite /prl_same_data ra rc rd ra' rc' rd' => - [ea eb ec].
by rewrite /prl_subfam_fct eb ec.
Qed.

  

Lemma prl_subsets_prop2 S  M (H:prl_subfam_hyp S M):
   projective_limit(projective_system_subsets H) = 
   projective_limit S \cap (productb M).
Proof.
move:(prl_subsets_prop H) => [pa pb pc pd].
rewrite {1}/projective_limit pa pc pd.
have dM: domain M = psI S by case: (H).
move:(prl_subfam_prop1 H) => [_ h2 _ _ _].
set_extens t.
  move=> /Zo_P [ha hb]; apply/setI2_P; split; last by exact.
  move:ha => /setXb_P[ua ub uc].
  rewrite dM in uc.
  have ha:inc t (productb (psE S)).
    apply/setXb_P; split => //.
      by rewrite ub dM ps_domain_E.
    rewrite ps_domain_E => i ii.
    by move: (H) => [_ _ hh _]; apply: (hh _ ii); apply: uc.
  apply/Zo_P; split => // i j lij.
  have xM: inc (Vg t j) (Vg M j).
    by apply: uc; rewrite - ps_substrate_r; order_tac.
  by rewrite - (h2 _ _ _ lij xM) - (hb _ _ lij).
move =>/setI2_P [/Zo_P [ha hb] tp]; apply/Zo_P; split; first exact.
move:tp => /setXb_P[ua ub uc].
move => i j lij.
have wp: inc (Vg t j) (Vg M j).
  by apply: uc; rewrite dM -(ps_substrate_r); order_tac.
by rewrite (h2 _ _ _ lij wp) - (hb _ _ lij).
Qed.

Definition prl_invim_set u x :=
  Lg (domain u) (fun i => (Vfi1 (Vg u i) (Vg x i))).


Lemma prl_inv_hyp S S' u x:
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  inc x (projective_limit S') ->
  prl_subfam_hyp S (prl_invim_set u x).
Proof.
move => ha[pa pb pc pd] /prl_limitP[fgx dx vx wx].
have ssI:=prl_same_index_same_I ha.
rewrite/prl_invim_set; split=> //; fprops; aw; trivial.
  move => i iS.
  move: (pc _ iS) => [fu su tu].
  have ra: sub (singleton (Vg x i)) (target (Vg u i)).
    by move => t /set1_P ->; rewrite tu; apply: vx; rewrite - ssI.
  rewrite - pb in iS; rewrite LgV //- su; exact:(sub_inv_im_source fu ra).
move => i j lij.  
move:(prl_prop0 lij)=> [idu jdu].
move: (pc _ idu) => [fui sui tui].
move: (pc _ jdu) => [fuj suj tuj].
move: (ps_function_f lij) => [ff sf tf].
have jde: inc j (domain (psE S')) by rewrite ps_domain_E - ssI.
have si1: sub (Vfi1 (Vg u j) (Vg x j))
      (source (Vg (psf S) (J i j))). 
  rewrite sf pr2_pair - suj; apply:(sub_inv_im_source fuj).
  by move => t /set1_P ->; rewrite tuj; apply: vx; rewrite - ssI.
move: (lij); rewrite ha => lij'.
move: (ps_function_f lij') => [ff' sf' tf'].
rewrite pr1_pair in tf;  rewrite pr2_pair in sf.
rewrite pr1_pair in tf';  rewrite pr2_pair in sf'.
have co1: Vg (psf S') (J i j) \coP Vg u j by split => //;rewrite sf' tuj.
have co2: Vg u i \coP Vg (psf S) (J i j) by split => //;rewrite tf sui.
rewrite !LgV// ? pb//; move => t. 
move/(Vf_image_P ff si1) => [z /(iim_fun_set1_P _ fuj) [za zb] ->].
apply/(iim_fun_set1_P _ fui); split.
  by rewrite sui - tf;  Wtac; rewrite sf - suj. 
move /(f_equal (Vf^~z)) :(pd _ _ lij); rewrite !compfV//.
  by move => ->; rewrite - zb; apply: wx.
by rewrite sf - suj.
Qed.



Lemma prl_inv_hyp_prop S S' u x
  (Hsb: prl_same_index S S') (Hc:  prl_map2_compat S S' u)
  (Hx: inc x (projective_limit S')):
  (Vfi1 (projective_limit_fun S S' u) x) =
  projective_limit (projective_system_subsets (prl_inv_hyp  Hsb Hc Hx)).
Proof.
rewrite prl_subsets_prop2.
move: (prl_map2_prop Hsb Hc); set pu := (projective_limit_fun S S' u).
move => [[fpu spu tpu] pup].
move:(prl_inv_hyp Hsb Hc Hx) =>[]; set g := (prl_invim_set u x). 
move => fgg dg gp1 gp2.
move:(Hc) => [fgu du up1 up2].
have ax1:= (prl_map_ax (prl_map2_prop1 Hsb Hc)).
have ssI: psI S = psI S' := prl_same_index_same_I Hsb.
set_extens t.
  move/(iim_fun_set1_P _ fpu) => [ts xv]; rewrite spu in ts.
  apply/setI2_P; split => //.
  move: xv; rewrite /pu /projective_limit_fun /projective_map /prl_map_val.
  aw; move => xv.
  move/prl_limitP: (ts) => [fgt st tv tp2].
  have dtdg: domain t = domain g by rewrite st dg.
  apply/setXb_P;split => //. 
  rewrite dg;  move => i idg.  
  have iI': inc i (psI S') by ue.
  have idu: inc i (domain u) by ue.
  rewrite /g /prl_invim_set LgV//.
  move: (up1 _ idg) => [fui sui tui].
  apply/(iim_fun_set1_P _ fui); rewrite sui; split => //.
     by apply: tv.
  by rewrite xv LfV // LgV//; apply: prl_map2_prop2.
move/setI2_P =>[ha hb].
apply/(iim_fun_set1_P _ fpu); rewrite spu; split => //. 
rewrite /pu /projective_limit_fun /projective_map LfV//.
move/prl_limitP:(Hx) => [fgx dx xv xp].
rewrite /prl_map_val.
apply:fgraph_exten.
+ done.
+ fprops.
+ by aw.
+ rewrite dx => i iI'.
  move:(iI'); rewrite - ssI => iI.
  have idu: inc i (domain u) by ue.
  move: (up1 _ iI) => [fui sui tui].
  move/setXb_P: hb => [ft dt tv].
  have idg: inc i (domain g)  by rewrite  dg.
  move: (tv _ idg); rewrite /g /prl_invim_set LgV//.
  by case/(iim_fun_set1_P _ fui) => _ ->; rewrite LgV // prl_map2_prop2.
Qed.

Lemma prl_inv_hyp_prop1 S S' u:
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  (forall i, inc i (psI S) -> injection (Vg u i)) ->
  injection (projective_limit_fun S S' u).
Proof.
move => h1 h2 h3.
move: (prl_map2_prop h1 h2) => [ [ff sf tf] _].
split =>// x y; rewrite sf => xlim ylim sv.
set up := (projective_limit_fun S S' u).
have hh: inc (Vf up x) (projective_limit S') by rewrite /up;  Wtac.
move:(prl_inv_hyp_prop h1 h2 hh);set uu := projective_limit _; move => h.
have: inc y uu by rewrite -h; apply/(iim_fun_set1_P _ ff); rewrite sf.
move/prl_limitP => [].
move:(prl_subsets_prop (prl_inv_hyp h1 h2 hh)) => [-> _ -> ->] fgy dy  yv _.
move/prl_limitP: (xlim) => [fgx dx xv _].
have dxdy: domain x = domain y by move/prl_limitP: (ylim) => [_ -> _ _]. 
rewrite - dy -dxdy in yv.
apply: fgraph_exten => // i idx.
move: (h2) => [h2a h2b h2c h2d].
have idu: inc i (domain u) by rewrite h2b -dx.
have iI: inc i (psI S) by rewrite -dx.
move: (h2c _ iI) => [fu su tu].
have ssI:= prl_same_index_same_I h1.
have iI': inc i (psI S') by rewrite  - ssI.
move: (yv _ idx); rewrite /prl_invim_set LgV//.
move/(iim_fun_set1_P _ fu); rewrite su; move => [sa].
move: (prl_map_ax (prl_map2_prop1 h1 h2)) => ax.
rewrite /up /projective_limit_fun /projective_map LfV//.
rewrite /prl_map_val LgV//  prl_map2_prop2 //. 
have xis : inc (Vg x i) (source (Vg u i))  by rewrite su; apply: xv.
have yis : inc (Vg y i) (source (Vg u i)) by rewrite su. 
by move:(proj2 (h3 _ iI) _ _ xis yis).
Qed.


Lemma prl_inv_hyp_prop2 S S' u:
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  (forall i, inc i (psI S) -> bijection (Vg u i)) ->
  bijection (projective_limit_fun S S' u).
Proof.
move => h1 h2 h3.
move: (prl_map2_prop h1 h2) => [ [ff sf tf] _].
split; first by apply:prl_inv_hyp_prop1 => // i /h3 [].
split =>// y; rewrite sf tf => yp.
move/prl_limitP: yp => [ghg dy yv yw].
have ssI:= prl_same_index_same_I h1.
have dy':  domain y = psI S by rewrite dy.
pose x:= Lg (psI S) (fun i => Vf (inverse_fun (Vg u i)) (Vg y i)).
have iii: psI S = domain (psE S) by rewrite ps_domain_E.
move: (h2) => [h2a h2b h2c h2d].
rewrite  - ssI in yv.
have xi i: inc i (psI S) -> inc (Vg x i) (Vg (psE S) i).
   move => iI; rewrite /x LgV//.
   move:(h3 _ iI) (h2c _ iI) => bu [fu su tu].
   by rewrite - su; apply: inverse_Vis => //; rewrite tu; apply: yv.
have xp: inc x (productb (psE S)).
   apply /setXb_P; rewrite /x - iii;aw; split; fprops.
have xps: inc x (projective_limit S).
  apply/Zo_P; split => // i j lij.
  have lij': gle (psr S') i j by rewrite - h1.
  move: (prl_prop0 lij) => [iI jI].
  move: (h2c _ iI) => [fui sui tui].
  move: (h2c _ jI) => [fuj suj tuj].
  have co1: Vg (psf S') (J i j) \coP Vg u j.
    move:(ps_function_f lij') => [fij sij tij].
    by split => //; rewrite sij tuj; aw.
  move:(ps_function_f lij) => [fij sij tij].
  have co2:Vg u i \coP Vg (psf S) (J i j).
    by split => //; rewrite sui tij; aw.
  have sx1: inc (Vg x j) (source (Vg u j)) by rewrite suj; apply: xi.
  have sx2: inc (Vg x j) (source (Vg (psf S) (J i j))).
    by rewrite sij; aw; apply: xi.
  have ys1: inc (Vg y j) (target (Vg u j)) by rewrite tuj; apply: yv.
  have ys2: inc (Vf (Vg (psf S) (J i j)) (Vg x j)) (source (Vg u i)).
    by rewrite pr1_pair in tij; rewrite sui - tij; apply: (Vf_target fij sx2).
  move:(f_equal (Vf^~(Vg x j)) (h2d _ _ lij)); rewrite !compfV//.
  have ->: Vf (Vg u j) (Vg x j) = Vg y j.
    by rewrite /x LgV// (inverse_V (h3 _ jI) ys1).
  rewrite - (yw _ _ lij') {2}/x LgV// => <-.
  by rewrite (inverse_V2 (h3 _ iI)).
move: (prl_map_ax (prl_map2_prop1 h1 h2)) => ax.
exists x => //.
rewrite /projective_limit_fun /projective_map LfV//.
symmetry;rewrite /prl_map_val - ssI; apply: fgraph_exten.
- fprops.
- done.
- by aw; rewrite dy'.
- aw => i iI.
  move: (h2c _ iI) => [fu su tu].
  rewrite LgV //(prl_map2_prop2 iI xps fu su) /x LgV// inverse_V //.
    exact: (h3 _ iI).
  by rewrite tu; apply: yv. 
Qed.

(** Direct image *)

Definition prl_dirim_set u :=
  Lg (domain u) (fun i => Imf (Vg u i)).

Lemma prl_direct_hyp S S' u:
  prl_same_index S S' ->  prl_map2_compat S S' u ->
  prl_subfam_hyp S' (prl_dirim_set u).
Proof.
move => pss [pa pb pc pd].
have ssI := (prl_same_index_same_I pss).
rewrite /prl_dirim_set; split.
- fprops.
- by  aw; rewrite pb ssI.
- move => i; rewrite - ssI => iI.
  have idu: inc i (domain u) by rewrite pb.  
  move:(pc _ iI) =>[fu su tu].
  by rewrite LgV // - tu; apply:Imf_Starget.
rewrite - pss pb;move => i j lij.
have lij':gle (psr S') i j by rewrite - pss.
move:(ps_function_f lij); aw  => - [fij sij tij].
move:(ps_function_f lij'); aw  => - [fij' sij' tij'].
move:(prl_prop0 lij)=> [iI jI].
move:(pc _ iI) =>[fui sui tui].
move:(pc _ jI) =>[fuj suj tuj].
have ss1: (sub (Imf (Vg u j)) (source (Vg (psf S') (J i j)))). 
  by rewrite sij' - tuj;apply:Imf_Starget.
have hb: Vg u i \coP Vg (psf S) (J i j).
  by split => //; rewrite sui tij; aw.
have hc: Vg (psf S') (J i j) \coP Vg u j.
  by split => //; rewrite sij' tuj.
move => t; rewrite ! LgV//.
move /(Vf_image_P fij' ss1) => [x /(Imf_P fuj) [y ya ->] ->].
have ysv: inc y (source (Vg (psf S) (J i j))) by  rewrite sij - suj.
move:(f_equal (Vf ^~y) (pd _ _ lij)); rewrite ! compfV//; move <-.
have hhh: inc (Vf (Vg (psf S) (J i j)) y) (source (Vg u i)).
  rewrite sui -tij; Wtac.
apply/(Imf_P fui); ex_tac.
Qed.


Lemma prl_dirim_prop S S' u
  (Hsb: prl_same_index S S') (Hc:  prl_map2_compat S S' u):
  sub (Imf (projective_limit_fun S S' u)) 
  (projective_limit (projective_system_subsets (prl_direct_hyp  Hsb Hc))).
Proof.
move => t.
move:(prl_map2_prop Hsb Hc) =>[ [fp sp tp] _].
move/(Imf_P fp) =>[x xt ->].
move: xt;rewrite sp => xd; move: (xd)=> /prl_limitP [fgx dx xv xp].
move: (prl_map_ax (prl_map2_prop1 Hsb Hc)) => ax.
rewrite /projective_limit_fun/projective_map LfV//.
rewrite /projective_limit /=.
set v :=  (prl_map_val S' (prl_map2_aux S u) x).
move:(Hc) => [hc1 hc2 hc3 hc4].
have ssI := prl_same_index_same_I Hsb.
apply/Zo_P; split.
  apply/setXb_P; rewrite /v/prl_map_val/prl_dirim_set; split.
  - fprops.
  - by aw; rewrite hc2 ssI.
  - aw; rewrite hc2; move => i iI.
    have iI': inc i (psI S') by rewrite - ssI.
    move:(hc3 _ iI) =>[fui sui tui].
    have aux: inc (Vg x i) (source (Vg u i)).
      by rewrite sui; apply: xv.
    rewrite LgV// (prl_map2_prop2 iI xd fui sui) LgV//. 
    by apply/(Imf_P fui); ex_tac.
move => i j lij.
move:(prl_prop0 lij) =>[iI' jI'].
have iI: inc i (psI S)  by rewrite ssI.
have jI: inc j (psI S)  by rewrite ssI.
move:(hc3 _ iI) =>[fui sui tui].
move:(hc3 _ jI) =>[fuj suj tuj]. 
have jdu: inc j (domain u) by rewrite hc2.
have aux: inc (Vg x j) (source (Vg u j))  by rewrite suj; apply: xv.
rewrite /v/prl_map_val LgV//.
rewrite  (prl_map2_prop2 iI xd fui sui).
rewrite LgV//  (prl_map2_prop2 jI xd fuj suj).
have hu: inc (Vf (Vg u j) (Vg x j)) (Vg (prl_dirim_set u) j).
   rewrite /prl_dirim_set LgV//.
   apply/(Imf_P fuj); ex_tac.
move:(prl_subfam_prop1 (prl_direct_hyp Hsb Hc)) => [_ k2 _ _ _]; rewrite k2 //.
rewrite -Hsb in lij;exact: (prl_map2_compat_aux Hsb Hc xd lij).
Qed.


Lemma right_directed_ind_prop r J:
  preorder r -> sub J (substrate r) -> right_directed_on r J ->
  right_directed_on (induced_order r J) J.
Proof.
move => or sr rdr x y xJ yJ.
move:(rdr _ _ xJ yJ) => [z [zJ za zb]]; exists z.
by split=> //;apply/iorder_gleP.
Qed.


Lemma prl_rest_can_cofinal_bf S J (H: sub J (psI S)):
  cofinal (psr S) J -> right_directed_on (psr S) J ->
  bijection (prl_restr_canonical H).
Proof.
move => pa pb.
move:(prl_restr_canonical_fp H) => [fg sg tg].
have ax:= (prl_restr_canonical_ax H).
move:(proj2 pa);rewrite ps_substrate_r => cof.
split.
  split => //; rewrite sg => x y xp yp.
  rewrite /prl_restr_canonical; aw => sr.
  move:(xp)(yp)=>/prl_limitP [xg dx xv xw]/prl_limitP[ yg dy yv yw].
  apply: fgraph_exten => //; rewrite dx // => i iI.
  move:(cof _ iI) =>[j jJ lij].
  rewrite (xw _ _ lij)  (yw _ _ lij); congr Vf.
  move:(f_equal (Vg^~j) sr); rewrite !LfV // !LgV//.
split => //; rewrite sg tg => y.
move: (prl_restr_prop H) => [pE pI pr pf].
move/prl_limitP =>[]; rewrite pE pr pf => yg yd yv yw.
have yi0 k: inc k J -> inc (Vg y k) (Vg (psE S) k).
  by move: yv; aw => yv kJ; move: (yv _ kJ); rewrite LgV.
pose idx i := choose (fun j => inc j J /\ gle (psr S) i j).
have idx1p i: inc i (psI S) ->  inc (idx i) J /\ gle (psr S) i (idx i).
  move/cof => [j ja jb].
  apply: (choose_pr (p:= (fun j => inc j J /\ gle (psr S) i j))); by exists j.
pose xi i := Vf (Vg (psf S) (Pair.J i (idx i))) (Vg y (idx i)).
have idx2 i j: inc j J -> gle (psr S) i j ->
               xi i = Vf (Vg (psf S) (Pair.J i j)) (Vg y j).
  move => jJ le1.
  move: (prl_prop0 le1) => [iI _].
  move:(idx1p _ iI) => [ixJ le2].
  move:(pb _ _ jJ ixJ) => [k [kJ le11 le22]].
  have le1': gle (induced_order (psr S) J) j k by apply/iorder_gleP.
  have le2': gle (induced_order (psr S) J) (idx i) k by  apply/iorder_gleP.
  rewrite /xi (yw _ _ le1') (yw _ _ le2') !LgV//.
  have yi: inc (Vg y k) (Vg (psE S) k) by apply: yi0.
  by rewrite (prl_prop3 le2 le22 yi) (prl_prop3 le1 le11 yi).
set x := Lg (psI S) xi.
have xp1: inc x (productb (psE S)).
  rewrite /x;apply/setXb_P;split; rewrite ? ps_domain_E; aww.
  move => i iI.
  move: (idx1p _ iI) => [sa sb].
  move:(ps_function_f sb); aw  => -[fij sij tij].
  by rewrite LgV ///xi -  tij; Wtac; rewrite sij; apply: yi0.
have xp: inc x (projective_limit S).
  apply/Zo_P; split => // i j lij.
  have [iI jI] := (prl_prop0 lij).
  move:(cof _ jI) => [k kJ ljk].
  have lik:= (proj33 (ps_preorder_r S) _ _ _ lij ljk).
  rewrite /x !LgV//; rewrite (idx2 _ _ kJ ljk) (idx2 _ _ kJ lik).
  exact (sym_eq (prl_prop3 lij ljk (yi0 _ kJ))).
have dy': J = domain y by rewrite yd; aw.
exists x => //;  rewrite /prl_restr_canonical LfV//.
symmetry;apply: fgraph_exten => //; aww => j jJ; rewrite LgV //.
move:(H _ jJ) => jI.
have lejj:=(prl_prop1 jI).
rewrite /x LgV// (idx2 j j jJ lejj) (prl_prop5 jI) //.
by move: (yv _ jJ); rewrite LgV.
Qed.

Lemma prl_singleton_I S: singletonp (psI S) ->
  projective_limit S = (productb (psE S)).
Proof.
move => [k Iv].
set_extens t; first by case/Zo_P.
move => tp; apply/Zo_P;split => // i j lij.
move:(prl_prop0 lij) => [iI jI].
move:(iI) jI; rewrite Iv => /set1_P ik /set1_P jk.
rewrite jk - ik (prl_prop5 iI) //.
by move/setXb_P:tp => [pa pb pc]; apply: pc; rewrite ps_domain_E.
Qed.

Lemma prl_singleton_prop S k
  (f := Lf (Vg ^~ k) (projective_limit S) (Vg (psE S) k)):
  inc k (psI S) -> (forall i, inc i (psI S) -> gle (psr S) i k) ->
   bijection_prop f (projective_limit S) (Vg (psE S) k).
Proof.
move => kI kg.
move: (prl_proj_ax kI) (prl_can_fun_fp kI) => ax ff.
rewrite /f;split; aw; trivial; apply:lf_bijective => //.
  move => x y /prl_limitP[g xd xv xw] /prl_limitP[yg yd yv yw] sv.
  apply:fgraph_exten => //; rewrite xd => // i iI.
  by rewrite (xw _ _  (kg _ iI))  (yw _ _  (kg _ iI)) sv.
move => y yk.
pose x := Lg (psI S) (fun i => Vf (Vg (psf S) (J i k)) y). 
have yvv: y = Vg x k by rewrite /x LgV// (ps_identity_f kI) idV.
exists x => //; rewrite/x;apply/prl_limitP; aw; split;fprops.
  move => i iI; rewrite LgV//.
  move:(ps_function_f  (kg _ iI)); aw => - [fij sik tik]; Wtac.
move => i j lij; move: (prl_prop0 lij) => [iI jI]; rewrite ! LgV//.
by rewrite(prl_prop3 lij (kg _ jI) yk).
Qed.

Definition prl_proj_image S i := Imf (prl_can_fun S i).
Definition prl_proj_image_fam S :=  Lg (psI S) (prl_proj_image S).

Lemma prl_proj_image_prop1 S i j:
  gle (psr S) i j ->
  sub (prl_proj_image S i) (Imf (Vg (psf S) (J i j))).
Proof.
move => lij.
move:(prl_prop0 lij) => [iI jI].
move: (prl_can_fun_fp iI) => [fi si ti].
move:(ps_function_f lij) => [fij sij tij].
move => t /(Imf_P fi) [u us ->].
have ax :=  (prl_proj_ax iI). 
rewrite si in us.
rewrite /prl_can_fun; aw; apply/(Imf_P fij);rewrite sij; aw; rewrite LfV//.
move/prl_limitP: (us) => [_  _ uv uw]; rewrite (uw _ _ lij).
move:(uv _ jI) => ha; ex_tac.
Qed.
  
Lemma prl_proj_image_prop2 S i:
  inc i (psI S) -> sub (prl_proj_image S i)  (Vg (psE S) i).
Proof.
move => iI.
move: (prl_can_fun_fp iI) => [ff sf tf].
move => t /(Imf_P ff); rewrite sf; move => [u up -> ].
have ax :=  (prl_proj_ax iI). 
move/prl_limitP: (up) => [_  _ uv _].
by rewrite /prl_can_fun LfV//; apply: uv.
Qed.
  
Lemma prl_proj_image_prop3 S: prl_subfam_hyp S (prl_proj_image_fam S).
Proof.
rewrite/prl_proj_image_fam; split; aww.
  by move => i iI; rewrite LgV//; apply: prl_proj_image_prop2.
move => i j lij;  move: (prl_prop0 lij) => [iI jI]; rewrite !LgV//.
move: (prl_can_fun_fp iI) => [fi si ti].
move: (prl_can_fun_fp jI) => [fj sj tj].
move: (ps_function_f lij); aw => - [fij sij tij].
move: (prl_proj_image_prop2  jI); rewrite - sij => hu.
move => t /(Vf_image_P fij hu) [u /(Imf_P fj) ].
rewrite sj ; move => [v vl -> ->].
have axj :=  (prl_proj_ax jI).
have axi :=  (prl_proj_ax iI).
apply/(Imf_P fi); rewrite si; exists v => //.
rewrite /prl_can_fun !LfV//; symmetry.
by move/prl_limitP: vl => [ _ _ _];apply.
Qed.

Lemma prl_proj_image_fam_fs S (fij' := prl_subfam_fct S (prl_proj_image_fam S)):
  forall ij, inc ij (psr S) -> surjection (Vg fij' ij).
Proof. 
move => ij ijr.
move:(prl_subfam_prop1 (prl_proj_image_prop3 S)).
rewrite -/fij'; move => [p1 p2 p3 p4 p5].
move:(p3 ij ijr) => [fij sij tij]; split => //.
move:(pr1_sr ijr) (pr2_sr ijr); rewrite ps_substrate_r => iI jI.
rewrite sij tij /prl_proj_image_fam  LgV//  LgV//.
move: ((proj31 (ps_preorder_r S)) _ ijr)  => pij.
move: (prl_can_fun_fp iI) => [fi si ti].
move: (prl_can_fun_fp jI) => [fj sj tj].
move => y /(Imf_P fi); rewrite si => - [u up ->].
have axi :=  (prl_proj_ax iI).
have axj :=  (prl_proj_ax jI).
have ra: inc (Vg u (Q ij)) (Imf (prl_can_fun S (Q ij))).
   apply /(Imf_P fj); rewrite sj.
   exists u => //; rewrite /prl_can_fun LfV//.
exists (Vg u (Q ij)) => //.
have rb: inc (Vg u (Q ij)) (Vg (prl_proj_image_fam S) (Q ij)).
  rewrite /prl_proj_image_fam ! LgV//.
rewrite - pij in ijr; move: (p2 _ _ (Vg u (Q ij)) ijr rb); rewrite{1} pij => ->.
rewrite /prl_can_fun LfV//.
by move/prl_limitP: up => [_ _ _ h]; rewrite - h.
Qed.

Lemma prl_proj_image_prop4 S:
  projective_limit S =
  projective_limit(projective_system_subsets (prl_proj_image_prop3 S)).
Proof.
move:(prl_subsets_prop  (prl_proj_image_prop3 S)) => [pa pb pc pd].
move:(prl_subfam_prop1  (prl_proj_image_prop3 S)) => [_ qb _ _ _]. 
set_extens t. 
   move=> tl; move/prl_limitP: (tl) => [ha hb hc hd].
   have Ha i : inc i (psI S) -> inc (Vg t i) (Vg (prl_proj_image_fam S) i).
     move =>  iI; rewrite /prl_proj_image_fam ! LgV//.
     move: (prl_can_fun_fp iI) => [fi si ti].
     apply/(Imf_P fi); rewrite si; exists t => //.
     have axi :=  (prl_proj_ax iI).
     rewrite /prl_can_fun LfV//.
   apply/prl_limitP; rewrite pa pb pc pd; split => //. 
   move => i j lij; move:(prl_prop0 lij) => [_ jI].
   by rewrite (qb _ _ _ lij (Ha _ jI)); apply: hd.
move/prl_limitP => [];rewrite pa pb pc pd => ha hv hc hd.
apply/prl_limitP; split => //. 
   move => i iI; move: (hc _ iI);rewrite /prl_proj_image_fam  LgV//.
   by apply:(prl_proj_image_prop2 iI).
move => i j lij;  move:(prl_prop0 lij) => [_ jI].
by move:(hd _ _ lij);rewrite /prl_proj_image_fam  qb //; apply: hc.
Qed.

Section Remark2.  
Variable S : projective_system.
Variables u F: Set.
Hypothesis compat: prl_map_compat S u F.
Hypothesis rdr:right_directed_on (psr S) (psI S).

Definition prl_r2_sf := prl_exa2_system F (ps_preorder_r S) (ps_substrate_r S).

Lemma prl_r2_sf_prop1:
 projective_system_on prl_r2_sf (cst_graph (psI S) F) (psI S) (psr S)
     (cst_graph (psr S) (identity F)).
Proof. apply:prl_exa2_prop. Qed.

Lemma prl_r2_sf_prop2:projective_limit prl_r2_sf = diagonal_graphp F (psI S). 
Proof. by apply:prl_exa2_prop2. Qed.

Lemma prl_r2_sf_prop3: prl_map2_compat prl_r2_sf S u.
Proof.
move:prl_r2_sf_prop1=> [vE vI vr vf].
move:(compat) => [cp1 cp2 cp3 cp4]; rewrite cp2 in cp3.
split => //;first by rewrite vI vE; move => i iI; rewrite LgV//; apply: cp3.
rewrite vf vr; move => i j lij.
move: (prl_prop0 lij)=> [iI jI].
move:(cp3 _ iI) => [fu su tu].
by rewrite (cp4 _ _ lij) LgV// - su;apply: (compf_id_r fu).
Qed.

Lemma prl_r2_sf_prop4 (lf:= (projective_limit prl_r2_sf))
      (ls:= (projective_limit S)) 
      (u1 := projective_map S u F)
      (u2 := projective_limit_fun  prl_r2_sf S u):
  [/\ function_prop u2 lf ls, function_prop u1  F ls &
      forall x, inc x F ->  Vf u1 x = Vf u2 (cst_graph (psI S) x)].
Proof.
have si: prl_same_index prl_r2_sf S by [].
have pa:=(prl_map2_prop si prl_r2_sf_prop3).
have pb: prl_map_property S u F u1  by apply: prl_map_prop.
split; [ by case: pa | by case: pb | move => x xF].
move:(prl_map_ax compat) => ax1.
have pc:inc (cst_graph (psI S) x) (projective_limit prl_r2_sf).
  rewrite  prl_r2_sf_prop2; apply/Zo_P; split.
     by apply: gfunctions_i1. 
  by rewrite /cst_graph;split; fprops; aw => a b aI bI; rewrite !LgV. 
have ax2 := (prl_map_ax (prl_map2_prop1 si prl_r2_sf_prop3)).
rewrite /u1 /u2  /projective_limit_fun  /projective_map !LfV//.
apply:Lg_exten => i iI /=.
move:(compat) => [_ p2 p3 _]; rewrite p2 in p3.
move:(p3 _ iI) =>[fui sui tui].
rewrite prl_map2_prop2 //= LgV//. 
Qed.


End Remark2.

(* noter *)
Lemma prl_restr_trivial p:
 Lf (restr^~ (psI p)) (projective_limit p) (projective_limit p) =
 identity (projective_limit p).
Proof.
set E := projective_limit p.
have pa x: inc x E ->  (restr x (psI p)) = x.
  move => xE; move/prl_limitP:(xE) => [fgx dx xv xw].
  by apply:fgraph_exten; fprops; aw; [ rewrite dx | aw => t tI; rewrite LgV//].
have pb: lf_axiom (restr^~ (psI p)) E E.
  by move => x xE; rewrite /= pa.
apply:function_exten;aww; first by apply:lf_function.
by move => x xE /=; rewrite  LfV // idV //  pa. 
Qed.

Lemma finite_subsets_order A (I:= Zo (\Po A) finite_set)
      (r:= sub_order I):
  [/\ order_on r I,
      forall x y, inc x I -> inc y I -> inc (x \cup y) I,
      forall x y, inc x I -> inc y I -> gle r x (x \cup y),
      forall i, inc i A -> inc (singleton i) I &
      right_directed r].
Proof.
move:(sub_osr I) => pa.
have hb: forall x y, inc x I -> inc y I -> inc (x \cup y) I.
  move => x y /Zo_P [/setP_P xI  /card_finite_setP xf]
            /Zo_P [/setP_P yI  /card_finite_setP yf].
  apply/Zo_P; split; first by apply/setP_P ;apply:setU2_12S.
  apply /card_finite_setP.
  move:(csum2_pr6 x y); rewrite - csum2cl - csum2cr => h.
  exact:(NS_le_nat h (NS_sum xf yf)).
have hc: forall x y, inc x I -> inc y I -> gle r x (x \cup y).
  move => x y xI yI; apply/sub_gleP; split => //; first by apply: hb.
  apply: subsetU2l.
split => //.
- move => i iI; apply/Zo_P; split; first by apply/setP_P => t /set1_P ->.
  by apply:set1_finite.
- move: pa => [or sr];apply/right_directedP; split => // x y xI yI.
  rewrite sr in xI yI.
  by exists(x\cup y); split; [ apply: hc | rewrite setU2_C; apply:hc].
Qed.


Section Remark3.
Variable S: projective_system.


Definition prl_r3_nI := Zo (\Po (psI S)) finite_set.
Definition prl_r3_nr := sub_order prl_r3_nI.

Lemma prl_r3_sr: substrate prl_r3_nr = prl_r3_nI.
Proof. exact: (proj2 (sub_osr _)). Qed.

Lemma prl_r3_trans i j k:
  gle prl_r3_nr i j ->  gle prl_r3_nr j k ->  gle prl_r3_nr i k.
Proof.
move => ha hb; move: (sub_osr prl_r3_nI) => [[_ _ tr _ ] _].
apply: (tr _ _ _ ha hb).
Qed.

Lemma prl_r3_nI_stable_union x y:
  inc x prl_r3_nI -> inc y prl_r3_nI -> inc (x \cup y) prl_r3_nI.
Proof. move: (finite_subsets_order (psI S)) => [_ h _ _ _]; apply: h. Qed.
  
Lemma prl_r3_directed_nr: right_directed prl_r3_nr.
Proof. by case: (finite_subsets_order (psI S)). Qed.

Lemma prl_r3_qprop0 i: inc i (psI S) -> inc (singleton i) prl_r3_nI. 
Proof. by move: i; case: (finite_subsets_order (psI S)). Qed.

Lemma prl_r3_qprop1 i j: gle (psr S) i j ->
     exists J, [/\ inc J  prl_r3_nI, inc i J & inc j J].
Proof.
move/prl_prop0 => [iI jI].
move:(prl_r3_nI_stable_union (prl_r3_qprop0 iI) (prl_r3_qprop0 jI)) => h.
exists (singleton i +s1 j); split;fprops.
Qed.
  
  
Lemma prl_r3_prop4 J: inc J prl_r3_nI -> sub J (psI S).
Proof. by move /Zo_P => [/setP_P]. Qed.

Definition prl_r3_systemi J :=
  match (ixm (inc J prl_r3_nI)) with
    | inl hx => prl_restr (prl_r3_prop4 hx)
    | inr _ => S
    end.
Definition prl_r3_Fl J := projective_limit (prl_r3_systemi J).

Definition prl_r3_gi J:= Lf (restr ^~ J) (projective_limit S) (prl_r3_Fl J).
Definition prl_r3_gij ij :=
  Lf (restr ^~ (P ij)) (prl_r3_Fl (Q ij)) (prl_r3_Fl (P ij)). 


Lemma prl_r3_res0 i (H: inc i prl_r3_nI):
  prl_r3_Fl i = (projective_limit (prl_restr (prl_r3_prop4 H))).
Proof.
by rewrite /prl_r3_Fl /prl_r3_systemi;case: (ixm (inc i prl_r3_nI)).
Qed.

Lemma prl_r3_prop5a j: inc j prl_r3_nI -> j = psI (prl_r3_systemi j).
Proof. by move => jL; rewrite /prl_r3_systemi; case: (ixm (inc j prl_r3_nI)).  Qed.

Lemma prl_r3_prop5b i (H: sub i (psI S)):
  inc i prl_r3_nI -> prl_same_data (prl_restr H) (prl_r3_systemi i).
Proof. by move => iL;rewrite /prl_r3_systemi; case: (ixm (inc i prl_r3_nI)). Qed.

Lemma prl_r3_res1 i: inc i prl_r3_nI ->
  function_prop (prl_r3_gi i) (projective_limit S) (prl_r3_Fl i).
Proof.
move => iL;rewrite /prl_r3_gi; rewrite prl_r3_res0; apply:prl_restr_canonical_fp.
Qed.

Lemma prl_r3_prop5 i j: gle prl_r3_nr i j ->  sub i (psI (prl_r3_systemi j)).
Proof.
by move/sub_gleP => [_ ha hb]; rewrite - (prl_r3_prop5a ha). 
Qed.

Lemma prl_r3_prop6 i j  (lij: gle prl_r3_nr i j) :
  prl_same_data (prl_restr (prl_r3_prop5 lij)) (prl_r3_systemi i).
Proof.
move/sub_gleP: (lij) => [iL jL r1].
have Hu:= (prl_r3_prop4 jL).
apply:prl_same_dataT (prl_r3_prop5b  (sub_trans r1 Hu) iL).
apply:prl_same_dataT  (projective_limit_restr_double_Iv Hu  r1).
apply:prl_restr_Iv2.
exact: (prl_same_dataS (prl_r3_prop5b Hu jL)).
Qed.

Lemma prl_r3_prop6a i j  (lij: gle prl_r3_nr i j) :
  (projective_limit_restr (prl_r3_prop5 lij)) = (prl_r3_Fl i).
Proof. apply:projective_limit_Iv;apply:prl_r3_prop6. Qed.

Lemma prl_r3_prop7 i j: gle prl_r3_nr i j ->
  lf_axiom (restr^~  i) (prl_r3_Fl j) (prl_r3_Fl i).
Proof.
move => lij; move: (prl_restr_canonical_ax (prl_r3_prop5 lij)).
by rewrite (prl_r3_prop6a lij).
Qed.

Lemma prl_r3_res2 i j: gle prl_r3_nr i j ->
  function_prop (prl_r3_gij (J i j)) (prl_r3_Fl j) (prl_r3_Fl i).
Proof.
move =>/prl_r3_prop7/lf_function ff; rewrite/prl_r3_gij; saw. 
Qed.

Lemma prl_r3_res3 i: inc i prl_r3_nI -> prl_r3_gij (J i i) = identity (prl_r3_Fl i).
Proof.
move => iL; rewrite /prl_r3_gij pr1_pair pr2_pair prl_r3_res0.
apply:prl_restr_trivial.
Qed.

Lemma prl_r3_pr4 i j k: gle prl_r3_nr i j ->  gle prl_r3_nr j k ->
   prl_r3_gij (J i j) \co prl_r3_gij (J j k) = prl_r3_gij (J i k).
Proof.
move => lij ljk.
have lik:= prl_r3_trans lij ljk.
move:(prl_r3_res2 lij) => [fij sij tij].
move:(prl_r3_res2 lik) => [fik sik tik].
move:(prl_r3_res2 ljk) => [fjk sjk tjk].
have cop: prl_r3_gij (J i j) \coP prl_r3_gij (J j k).
  by split => //; rewrite sij tjk.
apply:function_exten.
- by apply:compf_f.
- exact.
- by aw; rewrite sjk sik.
- by aw; rewrite tij tik.
- aw; rewrite sjk => x s.
  move:(prl_r3_prop7 lij)(prl_r3_prop7 lik)(prl_r3_prop7 ljk) => aij aik ajk. 
  have xs': inc x (source (prl_r3_gij (J j k)))  by rewrite sjk.
  rewrite compfV// /prl_r3_gij; aw.
  have suij: sub i j by case/sub_gleP:lij. 
  rewrite (LfV ajk s) !LfV // ? double_restr //;exact: (ajk _ s).
Qed.

Definition prl_r3_F: projective_system.
Proof.
apply:(@ProjectiveSystem (Lg prl_r3_nI prl_r3_Fl) prl_r3_nI prl_r3_nr (Lg prl_r3_nr prl_r3_gij)).
- apply: (order_preorder (proj1 (sub_osr _))).
- exact:prl_r3_sr.
- fprops.
- by aw.
- by fprops.
- by aw.
- move => p pL.
  have pp: pairp p by move/Zo_P: pL => [/setX_P []].
  move:(pr2_sr pL) (pr1_sr pL) ; rewrite prl_r3_sr => iL jL.
  rewrite ! LgV//;move:pL;rewrite -{1 2}pp => pL; apply: (prl_r3_res2 pL).
- move => i j k ha hb; rewrite !LgV//; first by apply:(prl_r3_pr4 ha hb).
  exact: (prl_r3_trans ha hb).
- move => i iL; move: (iL); rewrite -prl_r3_sr => iL'.
  have ii: inc (J i i) prl_r3_nr by  apply/sub_gleP; split;fprops.
  rewrite !LgV //; exact:(prl_r3_res3 iL).
Defined. 


Lemma prl_r3_F_prop: projective_system_on prl_r3_F
                    (Lg prl_r3_nI prl_r3_Fl) prl_r3_nI prl_r3_nr (Lg prl_r3_nr prl_r3_gij).
Proof. done. Qed.

Definition prl_r3_restr_fun z:=  Lg prl_r3_nI (restr z).

Definition prl_r3_F_can := Lf prl_r3_restr_fun
   (projective_limit S) (projective_limit prl_r3_F). 

Lemma prl_r3_F_can_ax1 i z: inc i prl_r3_nI -> inc z (projective_limit S) ->
   inc (restr z i) (prl_r3_Fl i).
Proof.
move => iL zp; move:(prl_restr_canonical_ax(prl_r3_prop4 iL) zp).
by congr inc; apply:projective_limit_Iv; apply:prl_r3_prop5b.
Qed.

Lemma prl_r3_F_can_ax: lf_axiom prl_r3_restr_fun
   (projective_limit S) (projective_limit prl_r3_F). 
Proof.
move: prl_r3_F_prop => [E_F I_F r_F f_F].
move => z zp.
move/prl_limitP:(zp) => [fgz dz zv zw].
rewrite /prl_r3_restr_fun;apply/prl_limitP; split.
- fprops.
- by aw.
- by rewrite E_F => i iL; rewrite !LgV//; apply: prl_r3_F_can_ax1.
- rewrite r_F f_F => i j lij.
  move/sub_gleP:(lij) => [iL jL s1].
  move: (prl_r3_prop7 lij) (prl_r3_F_can_ax1 jL zp) => ra rb.
  by rewrite /prl_r3_gij !LgV // pr1_pair pr2_pair LfV// double_restr.
Qed.

Lemma prl_r3_F_can_fun: inc prl_r3_F_can
  (functions (projective_limit S) (projective_limit prl_r3_F)). 
Proof.
rewrite /prl_r3_F_can;apply/functionsP; saw.
apply:lf_function; apply: prl_r3_F_can_ax.
Qed.

Lemma prl_r3_F_can_bf: bijection prl_r3_F_can.
Proof.
rewrite /prl_r3_F_can;apply:lf_bijective; first by apply: prl_r3_F_can_ax.
  move => u v upl vpl sr.
  move/prl_limitP:upl => [fgu du uv uw].
  move/prl_limitP:vpl => [fgv dv vv vw].
  have sdu: domain u = domain v by rewrite du dv.
  apply:(fgraph_exten fgu fgv sdu); rewrite du => j jI.
  move:(prl_r3_qprop0 jI)(set1_1 j) => sL jsj.
  move: (f_equal (fun z => Vg (Vg z (singleton j)) j) sr).
  rewrite /prl_r3_restr_fun !LgV//.
move => y yp.
move:prl_r3_F_prop => [E_F I_F r_F f_F].
have da: domain (psE prl_r3_F) = prl_r3_nI by  rewrite E_F; aw.
move/Zo_P:(yp)  => [/setXb_P [fgy dy yv] yw].
rewrite da in dy yv; rewrite r_F in yw; rewrite E_F in yv.
have yab a b: gle prl_r3_nr a b -> Vg y a = restr (Vg y b) a.
  move => lab;move: (yw _ _ lab); rewrite f_F LgV//.
  move:(prl_r3_prop7 lab) => ax1.
  move/(sub_gleP):lab => [_ bsr _].
  by rewrite/prl_r3_gij LfV//; aw; move: (yv b bsr);rewrite LgV //.
pose xi i := Vg (Vg y (singleton i)) i.
have idx2 i j: inc j prl_r3_nI -> inc i (psI S)-> inc i j -> xi i = Vg (Vg y j) i.
  move => jL iI ij.
  have siL:= prl_r3_qprop0 iI.
  have kL:= (prl_r3_nI_stable_union jL siL).
  have j1k:  gle prl_r3_nr j (j +s1 i) by apply/sub_gleP; split; fprops. 
  have j2k:  gle prl_r3_nr (singleton i) (j +s1 i).
    by apply/sub_gleP; split; fprops=> t /set1_P ->; fprops.
  move:(prl_r3_prop7 j1k) (prl_r3_prop7 j2k) (yv _ kL). 
  rewrite LgV// => ax1 ax2 ii. 
  rewrite /xi (yw _ _ j1k) (yw _ _ j2k) f_F  /prl_r3_gij !LgV//; aw.
  rewrite ! LfV// ! LgV//; fprops.
set x := Lg (psI S) xi.
have xx i  (iL: inc i prl_r3_nI):  
   inc (Vg y i) (projective_limit (prl_restr (prl_r3_prop4 iL))).
   move: (yv _ iL); rewrite LgV ///prl_r3_Fl /prl_r3_systemi.
   by case: (ixm (inc i prl_r3_nI)).
have xpe: inc x (productb (psE S)).
   apply/setXb_P; rewrite /x ps_domain_E ; split; aww.
   move => i iI; rewrite LgV//; have sa := (prl_r3_qprop0 iI).
   move/Zo_P:(xx _ sa).
   move: (prl_restr_prop (prl_r3_prop4 sa)) =>[ka kb kc kd]; rewrite ka kc kd.
   move => [] /setXb_P [fgu]; aw; move => du uv _.
   move: (uv _ (set1_1 i)); rewrite LgV; fprops.
have yve: y = prl_r3_restr_fun x.
  move/setXb_P: xpe =>[xa xb xc].
  rewrite /prl_r3_restr_fun;apply: fgraph_exten; aww.
  rewrite dy => i iL;move: (xx _ iL);move /Zo_P. 
  move: (prl_restr_prop (prl_r3_prop4 iL)) =>[ka kb kc kd]; rewrite ka kc kd.
  move => [] /setXb_P [fgu]; aw; move => dyi yip1 yip2; rewrite LgV//.
  apply: fgraph_exten => //; aww.
  rewrite dyi /x => j di;move/Zo_P:(iL) => [/setP_P h _]; move: (h _ di) => jI.
  by rewrite !LgV // (idx2 _ _ iL jI di).
exists x => //; apply/Zo_P; split => //.
move => i j lij.
move:(arg1_sr lij) (arg2_sr lij);rewrite ps_substrate_r => iI jI.
move: (prl_r3_qprop1 lij) => [J [jL iJ jJ]].
rewrite/x (LgV iI) (LgV jI) (idx2 _ _ jL iI iJ) (idx2 _ _ jL jI jJ).
have ll: gle(induced_order (psr S) J) i j by apply/iorder_gleP.
move: (xx _ jL) => /Zo_P [yp1 yp2].
by rewrite (yp2 _ _ ll)/prl_restr /= LgV.
Qed.

End Remark3.


Section DoubleProjInjLimit.
Variables I1 I2 r1 r2: Set.
Hypothesis (or1: preorder r1)(or2: preorder r2)
           (sr1: substrate r1 = I1)(sr2: substrate r2 = I2).

Lemma pidl_or:  preorder_on (prod_of_relation r1 r2) (I1 \times I2).
Proof.
split; first by apply:order_product2_preorder.
by move:(order_product2_sr1 or1 or2); rewrite sr1 sr2.
Qed.

Lemma pidl_gleP i j: gle (prod_of_relation r1 r2) i j <->
   [/\ pairp i, pairp j, gle r1 (P i) (P j) & gle r2 (Q i) (Q j)].
Proof. apply:prod_of_rel_P. Qed.


Lemma pidl_gleP1 i j k l: gle (prod_of_relation r1 r2) (J i j) (J k l) <->
  gle r1 i k /\ gle r2  j l.
Proof.
split; first  by move/pidl_gleP => [_ _ ] ; aw.
move => [ha hb]; apply/pidl_gleP; split; aww.
Qed.

Lemma pidl_i1_L a b: gle r2 a b -> inc a I2.
Proof. by move/arg1_sr; rewrite sr2. Qed.

Lemma pidl_i2_L a b: gle r2 a b -> inc b I2.
Proof. by move/arg2_sr; rewrite sr2. Qed.

Fact pidl_i3_L x: inc x r2 -> gle r2  (P x) (Q x).
Proof. by move => xr2; rewrite /gle/related (proj31 or2 _ xr2). Qed.

Lemma pidl_directed: 
  right_directed_prop r1 -> right_directed_prop r2 ->
  right_directed_prop (prod_of_relation r1 r2).
Proof.
move => dr1 dr2 x y; rewrite (order_product2_sr1 or1 or2).
move => /setX_P [px Px Qx] /setX_P [py Py Qy].
move:(dr1 _ _ Px Py) (dr2 _ _ Qx Qy)=> [a [pa pb]] [b [pc pd]].
exists (J a b);split; apply/pidl_gleP;aw; split; fprops.
Qed.



Lemma pidl_directed_bis: nonempty I1 -> nonempty I2 ->
  right_directed_prop (prod_of_relation r1 r2) ->
  right_directed_prop r1 /\ right_directed_prop r2.
Proof.
move:pidl_or => [orp srp].
move => [a aiI] [b bI2] h; split => x y xsr ysr.
   have jxbs : inc (J x b) (substrate ((prod_of_relation r1 r2))).
      rewrite srp - sr1; fprops.
   have jybs : inc (J y b) (substrate ((prod_of_relation r1 r2))).
      rewrite srp - sr1; fprops.
  move:(h _ _ jxbs jybs) => [z [/pidl_gleP [_ _ za _] /pidl_gleP [_ _ zb _]]].
  by move: za zb; aw => za zb; exists (P z).
have jxbs : inc (J a x) (substrate ((prod_of_relation r1 r2))).
      rewrite srp - sr2; fprops.
have jybs : inc (J a y) (substrate ((prod_of_relation r1 r2))).
      rewrite srp - sr2; fprops.
move:(h _ _ jxbs jybs) => [z [/pidl_gleP [_ _ _ za] /pidl_gleP [_ _ _ zb]]].
by move: za zb; aw => za zb; exists (Q z).
Qed.

End DoubleProjInjLimit.

Section DoubleProjectiveLimit.
Variables I1 I2 r1 r2: Set.
Hypothesis (or1: preorder r1)(or2: preorder r2)
           (sr1: substrate r1 = I1)(sr2: substrate r2 = I2).

Variable S: projective_system.
Hypothesis Sr: psr S = (prod_of_relation r1 r2).

Lemma prl_dl_I: psI S = I1 \times I2.
Proof. by rewrite - ps_substrate_r Sr (proj2 (pidl_or or1 or2 sr1 sr2)). Qed.

Definition prl_dl_Elam_fam lam := Lg I1 (fun i => Vg (psE S) (J i lam)).
Definition prl_dl_glam_fam lam :=
  Lg r1 (fun ij => Vg (psf S) (J (J (P ij) lam) (J (Q ij) lam))).

Lemma prl_dl_index_p1 lam i: inc lam I2 -> inc i r1 ->
   gle (psr S) (J (P i) lam) (J (Q i) lam). 
Proof.
move => ha hb; rewrite Sr; apply/pidl_gleP1; split.
  by rewrite/gle /related (proj31 or1 _ hb).
by apply:(proj32 or2 lam); rewrite sr2.
Qed.


Lemma prl_dl_index_p2 lam mu i:  gle r2 lam mu -> inc i I1 ->
   gle (psr S) (J i lam) (J i mu).
Proof.
move => ha hb;  rewrite Sr;  apply/pidl_gleP1; split => //.
by apply: (proj32 or1); rewrite sr1.
Qed.                                                            


Definition prl_dl_S_lambda lam (Hl: inc lam I2) : projective_system.
Proof.
apply(@ProjectiveSystem (prl_dl_Elam_fam lam) I1 r1 (prl_dl_glam_fam lam)).
- done.
- done.
- rewrite /prl_dl_Elam_fam; fprops.
- by rewrite /prl_dl_Elam_fam; aw.
- rewrite /prl_dl_glam_fam; fprops.
- by rewrite /prl_dl_glam_fam; aw.
  move => i iI.
  move:(pr1_sr iI)(pr2_sr iI); rewrite sr1 => piI qiI.
  rewrite /prl_dl_glam_fam /prl_dl_Elam_fam !LgV//.
  by move:(ps_function_f (prl_dl_index_p1 Hl iI)); aw. 
- move => i j k lij ljk.
  have lik: gle r1 i k by exact: (proj33 or1 _ _ _ lij ljk).
  move:(prl_dl_index_p1 Hl lij) (prl_dl_index_p1 Hl ljk).
  rewrite/prl_dl_glam_fam. rewrite !LgV//; aw; apply:(ps_compose_f). 
- move => i iI.
  have pp: inc (J i lam) (psI S) by rewrite prl_dl_I; apply:setXp_i.
  have iir: inc (J i i) r1 by apply: (proj32 or1 i); rewrite sr1.
    by move:(ps_identity_f pp); rewrite /prl_dl_glam_fam /prl_dl_Elam_fam
      !LgV//; aw.
Defined.

Lemma prl_dl_S_lambda_prop lam (Hl: inc lam I2) :
  projective_system_on (prl_dl_S_lambda Hl)
     (prl_dl_Elam_fam lam) I1 r1 (prl_dl_glam_fam lam).
Proof. by []. Qed.

Definition prl_dl_system_S_lambda lam :=
  match (ixm (inc lam I2)) with
    | inl hx => (prl_dl_S_lambda hx)
    | inr _ => S
    end.

Definition prl_dl_F_lambda lam :=
  projective_limit (prl_dl_system_S_lambda lam).

Lemma prl_dl_F_lambda_prop lam (Hl: inc lam I2): 
  prl_dl_F_lambda lam = projective_limit (prl_dl_S_lambda Hl).
Proof.
rewrite /prl_dl_F_lambda /prl_dl_system_S_lambda.
by case: (ixm (inc lam I2)).
Qed.

Definition prl_dl_halm_fam lam mu:=
  Lg I1 (fun i => Vg (psf S) (J (J i lam) (J i mu))).

Definition prl_dl_hlm lam mu (H: gle r2 lam mu) :=
  projective_limit_fun (prl_dl_S_lambda (pidl_i2_L sr2 H))
                       (prl_dl_S_lambda (pidl_i1_L sr2 H))
                       (prl_dl_halm_fam lam mu).


Lemma prl_dl_halm_compat lam mu (H: gle r2 lam mu):
  prl_map2_compat (prl_dl_S_lambda (pidl_i2_L sr2 H))
                 (prl_dl_S_lambda (pidl_i1_L sr2 H)) (prl_dl_halm_fam lam mu).
Proof.
rewrite /prl_dl_halm_fam;split.
- fprops.
- by aw.
- move => i /= iI; rewrite /prl_dl_Elam_fam !LgV//.
  by move:(ps_function_f(prl_dl_index_p2 H iI)); aw.
- move => i j /= leij.
  move:(arg1_sr leij)(arg2_sr leij); rewrite sr1 => iI jI.
  rewrite /prl_dl_glam_fam ! LgV//; aw.
  move:(prl_dl_index_p2 H iI)(prl_dl_index_p2 H jI) => lea led.
  move: (prl_dl_index_p1  (pidl_i2_L sr2 H) leij); aw => leb.
  move: (prl_dl_index_p1  (pidl_i1_L sr2 H) leij); aw => lec.
  by rewrite (ps_compose_f lea leb) (ps_compose_f lec led).
Qed.

Lemma prl_dl_i12L a b (H: gle r2 a b):
  prl_same_index (prl_dl_S_lambda (pidl_i2_L sr2 H))
                 (prl_dl_S_lambda (pidl_i1_L sr2 H)).
Proof. by []. Qed.

Lemma prl_dl_hlm_compose l m n
  (Hlm : gle r2 l m) (Hmn: gle r2 m n):
  (prl_dl_hlm Hlm)  \co (prl_dl_hlm Hmn) =
  (prl_dl_hlm (proj33 or2 _ _ _ Hlm Hmn)).
Proof.
move:(prl_dl_halm_compat Hlm) (prl_dl_halm_compat Hmn).
set S1 := (prl_dl_S_lambda (pidl_i1_L sr2 Hlm)).
set S2 := (prl_dl_S_lambda (pidl_i2_L sr2 Hlm)).
set S3 := (prl_dl_S_lambda (pidl_i1_L sr2 Hmn)).
set S4 := (prl_dl_S_lambda (pidl_i2_L sr2 Hmn)).
move => h1 h2.
have dS2S3: prl_same_data S2 S3 by [].
have h2': prl_map2_compat S4 S2 (prl_dl_halm_fam m n) by exact: h2.
have sd1: prl_same_index S4 S2 by [].
have sd2: prl_same_index S2 S1 by [].
rewrite -(proj2(prl_map2_compose sd1 sd2 h2' h1)).
rewrite /prl_dl_hlm.
set u := Lg _ _.
have -> //: u = (prl_dl_halm_fam l n).
rewrite /prl_dl_halm_fam /u; apply: Lg_exten => // i iI.
by rewrite /prl_dl_halm_fam !LgV//; apply: ps_compose_f; apply:prl_dl_index_p2.
Qed.


Definition prl_dl_hlm_gen x :=
  match (ixm (inc x r2)) with
    | inl hx => (prl_dl_hlm (pidl_i3_L or2 hx))
    | inr _ => emptyset
    end.

Lemma prl_dl_hlm_fct lm: inc lm r2 ->
   function_prop (prl_dl_hlm_gen lm)
         (prl_dl_F_lambda (Q lm))(prl_dl_F_lambda (P lm)).
Proof.
move => lemn.
move: (pidl_i3_L or2 lemn) => H.
move:(proj1 (prl_map2_prop (prl_dl_i12L H) (prl_dl_halm_compat H))).
move:(pidl_i1_L sr2 H)(pidl_i2_L sr2 H) => p1I p2I.
rewrite (prl_dl_F_lambda_prop p1I)(prl_dl_F_lambda_prop p2I).
by rewrite /prl_dl_hlm_gen; case: (ixm (inc lm r2)).
Qed.

Lemma prl_dl_S_lambda_Iv2 x y  (H1: inc x I2) (H2: inc y I2) : x = y ->
  prl_same_data (prl_dl_S_lambda H1)(prl_dl_S_lambda H2).
Proof. 
move => exy.
move:(prl_dl_S_lambda_prop H1) (prl_dl_S_lambda_prop H2).
rewrite /prl_same_data.
by move => [ -> _ -> ->] [ -> _ -> ->]; rewrite exy.
Qed.

Lemma  prl_dl_hml_invariant i j (H:gle r2 i j) :
   prl_dl_hlm H = prl_dl_hlm_gen (J i j).
Proof.
rewrite /prl_dl_hlm_gen.
case: (ixm (inc (J i j) r2)) => // h.
apply:prl_projective_limit_fun_IV2.
- by apply:prl_dl_S_lambda_Iv2; aw.
- by apply:prl_dl_S_lambda_Iv2; aw.
- by aw.
Qed.

Lemma prl_dl_hml_id i: inc i I2 ->
   Vg (Lg r2 prl_dl_hlm_gen) (J i i) = identity (prl_dl_F_lambda i).
Proof.
move => i2.
have iir: inc (J i i) r2 by apply: (proj32 or2 i); rewrite sr2.
rewrite LgV // prl_dl_F_lambda_prop.
set S1 :=  (prl_dl_S_lambda (pidl_i1_L sr2 iir)).
set S2 :=  (prl_dl_S_lambda (pidl_i2_L sr2 iir)).
have ha: (prl_same_index S1 S2) by [].
have hb:=(prl_dl_halm_compat iir).
move:(prl_map2_prop ha hb).
set f := projective_limit_fun _ _ _.
have <-: f = prl_dl_hlm_gen (J i i) by apply:(prl_dl_hml_invariant iir).
move => [[ff sf tf] fp].
apply:function_exten.
- done.
- fprops.
- by aw.
- by aw.
- rewrite sf => x xl; rewrite idV //.
  have fxl: inc (Vf f x) (projective_limit S2) by  Wtac.
  move/prl_limitP: (xl) => [xa xb xc xd].
  move/prl_limitP: fxl => [xa' xb' xc' xd'].
  apply: fgraph_exten => //; rewrite ? xb xb' // => j jI2.
  move:(prl_map_val_aux2 ha hb jI2 xl).
  have hu: inc (J j i) (psI S)  by rewrite prl_dl_I; apply/setXp_i.
  move:  (prl_dl_S_lambda_prop (pidl_i1_L sr2 iir)). rewrite -/S1.
  move => [s1E s1I s1r s1f].
  have h1: inc (Vg x j) (Vg (psE S) (J j i)).
     by move:(xc _ jI2);  rewrite s1E /prl_dl_Elam_fam LgV//.
  have ji1: inc j I1 by rewrite - s1I.
  rewrite /prl_dl_halm_fam (LgV jI2) (prl_prop5 hu h1).
  by rewrite - (prl_map_val_aux2  ha (prl_dl_halm_compat iir) jI2 xl).  
Qed.

Definition prl_dl_systemS': projective_system.
Proof.
apply(@ProjectiveSystem (Lg I2 prl_dl_F_lambda) I2 r2 (Lg r2 prl_dl_hlm_gen)).
- done.
- done.                          
- fprops.
- by aw.
- fprops.
- by aw.
- move => i i2; move: (pr1_sr i2)(pr2_sr i2); rewrite sr2 => iI jI.
  rewrite !LgV//; apply:(prl_dl_hlm_fct i2).
- move => i j k lij ljk.
  move:(proj33 or2 _ _ _ lij ljk) => lkj; rewrite !LgV//.
  move:(prl_dl_hlm_compose lij ljk).
  by rewrite 3!(prl_dl_hml_invariant).
- move => i i2; rewrite (prl_dl_hml_id i2); rewrite LgV//.
Defined.

Lemma  prl_dl_systemS'_prop: projective_system_on prl_dl_systemS'
     (Lg I2 prl_dl_F_lambda) I2 r2 (Lg r2 prl_dl_hlm_gen).
Proof. by []. Qed.

Definition prl_dl_slice x l := Lg I1 (fun i => Vg x (J i l)). 
Definition prl_dl_slice2 x := Lg I2 (prl_dl_slice x).
Definition prl_dl_can_iso := Lf prl_dl_slice2 
   (projective_limit S) (projective_limit prl_dl_systemS').

Lemma prl_dl_slice_p1 x lam: inc x (projective_limit S) ->
  inc lam I2 -> inc (prl_dl_slice x lam) (prl_dl_F_lambda lam).
Proof.
move => xl lI;rewrite (prl_dl_F_lambda_prop).
move: (prl_dl_S_lambda_prop lI) =>[E_S I_S r_S f_S].
move/prl_limitP: (xl) => [xa xb xc xd].
rewrite /prl_dl_slice; apply/prl_limitP; rewrite I_S E_S r_S f_S; split.
- fprops.
- by aw.
- move => i iI;rewrite /prl_dl_Elam_fam !LgV//; apply: xc.
  by rewrite prl_dl_I; apply:setXp_i.
- move => i j leij;rewrite /prl_dl_Elam_fam.
  move: (arg1_sr leij) (arg2_sr leij); rewrite sr1 => iI jI.
  rewrite /prl_dl_glam_fam !LgV//; aw;apply:xd.
  rewrite Sr; apply/pidl_gleP1; split => //.
  by apply: (proj32 or2); rewrite sr2.
Qed.
  
Lemma prl_dl_slice_p2 x: inc x (projective_limit S) ->
  inc (prl_dl_slice2 x) (projective_limit prl_dl_systemS').
Proof.
move=> xp.
move:prl_dl_systemS'_prop => [E_S I_S r_S f_S].
rewrite /prl_dl_slice2;apply/prl_limitP; rewrite I_S E_S r_S f_S; split.
- fprops.
- by aw.
- by move => i iI; rewrite !LgV//; apply:  prl_dl_slice_p1.
- move => i j leij.
  move: (arg1_sr leij) (arg2_sr leij); rewrite sr2 => iI jI.
  move:(prl_dl_slice_p1 xp iI) (prl_dl_slice_p1 xp jI).
  move:(prl_dl_hlm_fct leij); aw; rewrite !LgV//.
  rewrite 2! prl_dl_F_lambda_prop.
  set Fj := projective_limit _; set Fi := projective_limit _.
  rewrite - prl_dl_hml_invariant; move => [ff sf tf] aFi bFj.
  have ha: inc (Vf (prl_dl_hlm leij) (prl_dl_slice x j))  Fi by  Wtac.
  move/prl_limitP: (aFi) => [xa xb xc xd].
  move/prl_limitP: (ha) => [ya yb yc yd].
  apply:fgraph_exten => //; first by rewrite xb yb.
  move: (prl_dl_S_lambda_prop iI) =>[vE1 vI1 vr1 vf1].
  rewrite xb /= => k kI.
  have hb :=(prl_dl_halm_compat leij).
  rewrite  /prl_dl_hlm. 
  set S1 := prl_dl_S_lambda _; set S2 := prl_dl_S_lambda _. 
  have hc: (prl_same_index S1 S2) by [].
  rewrite -(prl_map_val_aux2  hc hb kI bFj)/prl_dl_slice /prl_dl_halm_fam !LgV//.
  move /prl_limitP: xp => [_ _ _]; apply;rewrite Sr.
  apply/pidl_gleP1; split => //.
  by apply: (proj32 or1); rewrite sr1.
Qed.  
  
Lemma prl_dl_canon_bijection: bijection_prop prl_dl_can_iso
   (projective_limit S) (projective_limit prl_dl_systemS').
Proof.
rewrite /prl_dl_can_iso; saw; apply:lf_bijective.
- apply:prl_dl_slice_p2.  
- move => u v ul vl sv.
  move /prl_limitP: (ul) => [ua ub uc ud].
  move /prl_limitP: (vl) => [va vb vc vd].
  apply/fgraph_exten => //; first by rewrite vb.
  rewrite ub prl_dl_I; move => p /setX_P [pp iI lL].
  move:(f_equal (fun z => Vg (Vg z (Q p)) (P p))  sv).
  by rewrite /prl_dl_slice2 /prl_dl_slice; rewrite !LgV // pp.
move => y yl.
pose x := Lg (psI S) (fun p =>  Vg (Vg y (Q p)) (P p)).
move/prl_limitP: (yl) => [].
move: prl_dl_systemS'_prop => [ES IS rS fS].
rewrite ES IS rS fS => ya yb yc yd.
have xa: fgraph x by rewrite /x; fprops.
have xb: domain x = psI S by rewrite /x; aw.
have xc i:inc i (psI S) -> inc (Vg x i) (Vg (psE S) i).
  rewrite /x =>  iI; rewrite LgV//.
  move: iI; rewrite prl_dl_I => /setX_P [pi i1I i2I]. 
  move:(yc _ i2I); rewrite LgV //prl_dl_F_lambda_prop. 
  move:(prl_dl_S_lambda_prop i2I) => [Esj Isj rsj fsj].
  move/ (prl_limitP);rewrite Esj Isj;move => [_ _ yic _].
  by move: (yic _ i1I);  rewrite /prl_dl_Elam_fam LgV// pi.
have xd i j: gle (psr S) i j -> Vg x i = Vf (Vg (psf S) (J i j)) (Vg x j).
  move => lp1p2; rewrite /x.
  move:(arg1_sr lp1p2) (arg2_sr lp1p2); rewrite ps_substrate_r => iI jI.
  rewrite ! LgV//. 
  move: iI jI; rewrite prl_dl_I => /setX_P [pi i1I i2I] /setX_P [pj j1I j2I].
  move:lp1p2; rewrite Sr => /pidl_gleP [_ _ leI leL].
  rewrite (yd _ _ leL) LgV//-prl_dl_hml_invariant /prl_dl_hlm. 
  move: (yc _ j2I); rewrite LgV// (prl_dl_F_lambda_prop (pidl_i2_L sr2 leL)).
  set S1 := prl_dl_S_lambda _;  set S2 := prl_dl_S_lambda _ => yjp.
  have ha: prl_same_index S1 S2 by [].
  have hb :=(prl_dl_halm_compat leL).
  rewrite - (prl_map_val_aux2 ha hb i1I yjp) /prl_dl_halm_fam LgV//.
  move: (yc _ j2I);rewrite LgV // prl_dl_F_lambda_prop => /prl_limitP [].
  move:(prl_dl_S_lambda_prop j2I) => [Esj Isj rsj fsj].
  rewrite Esj Isj rsj fsj => yja yjb yjc yjd.
  have hc: gle (psr S) (J (P i) (Q i)) (J (P i) (Q j)).  
    rewrite Sr; apply/pidl_gleP1; split => //.
    by apply: (proj32 or1); rewrite sr1.
  have hd: gle (psr S) (J (P i) (Q j)) (J (P j) (Q j)). 
    rewrite Sr; apply/pidl_gleP1; split => //.
    by apply: (proj32 or2); rewrite sr2.
  rewrite (yjd _ _ leI) /prl_dl_glam_fam LgV//; aw.
  rewrite -[in J i j] pj -[in (J i (J (P j) (Q j)))] pi.
  rewrite (prl_prop3 hc hd) //.
  move: (yjc _ j1I); rewrite /prl_dl_Elam_fam LgV//.
exists x; first by apply/prl_limitP.
rewrite/prl_dl_slice2/prl_dl_slice /x.
apply:fgraph_exten; aww.
rewrite yb => l lL; move:(yc _ lL); move: lL; simpl => lL.
rewrite /prl_dl_F_lambda ! LgV//; move/prl_limitP => [yla ylb ylc yld].
have ha:psI (prl_dl_system_S_lambda l) = I1.
  by rewrite /prl_dl_system_S_lambda; case: (ixm (inc l I2)).
rewrite ha in ylb.
apply:fgraph_exten; fprops; rewrite ylb; aw; trivial.
move => i iI2 /=; rewrite !LgV//; aw; trivial.
by rewrite prl_dl_I; apply: setXp_i.
Qed.

End DoubleProjectiveLimit.


Section  DoubleInverseLimit2.

Variables I1 I2 r1 r2: Set.
Hypothesis (or1: preorder r1)(or2: preorder r2)
           (sr1: substrate r1 = I1)(sr2: substrate r2 = I2).

Variables S S': projective_system.
Variable u: Set.
Hypothesis Sr: psr S = prod_of_relation r1 r2.
Hypothesis Sr': psr S' = prod_of_relation r1 r2.
Hypothesis compat_u: prl_map2_compat S S' u.

Lemma psr_dl2_SrSr: prl_same_index S S'. 
Proof. by rewrite/prl_same_index Sr Sr'. Qed.


Definition prl_dl2_ulam_fam lam :=  Lg I1 (fun i => Vg u (J i lam)).
Definition prl_dl2_Slambda := (prl_dl_system_S_lambda or1 or2 sr1 sr2 Sr).
Definition prl_dl2_Slambda' := (prl_dl_system_S_lambda or1 or2 sr1 sr2 Sr').

Lemma prl_dl2_res1 lam:inc lam I2 ->
   prl_same_index (prl_dl2_Slambda lam) (prl_dl2_Slambda' lam) /\
   prl_map2_compat (prl_dl2_Slambda lam) (prl_dl2_Slambda' lam)
                  (prl_dl2_ulam_fam lam).
Proof.
move => li2.
rewrite /prl_same_index/prl_map2_compat.
set S1 := (prl_dl_S_lambda  or1 or2 sr1 sr2 Sr li2).
set S2 := (prl_dl_S_lambda  or1 or2 sr1 sr2 Sr' li2).
have [ES1 rS1 fS1]: prl_same_data (prl_dl2_Slambda  lam) S1.
    rewrite/prl_dl2_Slambda/prl_dl_system_S_lambda.
    by case: (ixm (inc lam I2)).
have [ES2 rS2 fS2]: prl_same_data (prl_dl2_Slambda' lam) S2.
    rewrite/prl_dl2_Slambda'/prl_dl_system_S_lambda.
    by case: (ixm (inc lam I2)).
rewrite/prl_same_index rS1 rS2.
split; first exact.
have ->: psI (prl_dl2_Slambda lam) = I1.
  by rewrite - ps_domain_E ES1 /= /prl_dl_Elam_fam;aw.
rewrite /prl_dl2_ulam_fam ES1 ES2; split.
+ fprops.
+ by aw.
+ move => i iI1; rewrite /= /prl_dl_Elam_fam ! LgV//.
  have ilI: inc (J i lam) (psI S).
    by rewrite -ps_substrate_r Sr (proj2(pidl_or or1 or2 sr1 sr2)); fprops.
  exact:(proj43 compat_u _ ilI).
+ move => i j lij; rewrite fS1 fS2.
  move:(prl_prop0 lij) => [iI jI].
  rewrite /= /prl_dl_glam_fam ! LgV//; aw.
  apply:(proj44 compat_u  (J i lam)  (J j lam)). 
  rewrite Sr; apply/pidl_gleP; split;aw; fprops.
  apply:(proj32 or2); ue.
Qed.

Definition prl_dl2_v lam :=
   projective_limit_fun (prl_dl2_Slambda lam) (prl_dl2_Slambda' lam)
                  (prl_dl2_ulam_fam lam).
Definition prl_dl2_v_fam := Lg I2 prl_dl2_v. 


Definition prl_dl2_limlim := (prl_dl_systemS' or1 or2 sr1 sr2 Sr).
Definition prl_dl2_limlim' := (prl_dl_systemS' or1 or2 sr1 sr2 Sr').

Lemma prl_dl2_res2:
  prl_map2_compat prl_dl2_limlim  prl_dl2_limlim' prl_dl2_v_fam.
Proof.
rewrite /prl_dl2_v_fam; split.
- fprops.
- by aw.
- move => i /= iI2; rewrite !LgV//.
  move:(prl_dl2_res1 iI2) => [ha hb].
  exact: (proj1 (prl_map2_prop ha hb)).
- move => i j /= leij'.
move:(arg1_sr leij')(arg2_sr leij'); rewrite sr2 => iI2 jI2.
rewrite !LgV // /prl_dl_hlm_gen; case: (ixm (inc (J i j) r2)) => // leij.
clear leij'.
set V := prl_dl2_v.
set hlm := prl_dl_hlm or1 or2 sr1 sr2 Sr (pidl_i3_L or2 leij).
set hlm' := prl_dl_hlm or1 or2 sr1 sr2 Sr' (pidl_i3_L or2 leij).
move:(prl_dl2_res1 iI2)(prl_dl2_res1 jI2) =>[ha hb][ha' hb'].
move: (prl_map2_prop3 ha hb) (prl_map2_prop3 ha' hb').
simpl. rewrite -/(prl_dl2_v _) -/(prl_dl2_v _) -/V.
set Si := projective_limit _; set Si' := projective_limit _.
set Sj := projective_limit _; set Sj' := projective_limit _.
move => [[fvi svi tvi]  Vip] [[fvj svj tvj] Vjp].

set T := prl_dl_S_lambda or1 or2 sr1 sr2 Sr. 
set T' := prl_dl_S_lambda or1 or2 sr1 sr2 Sr'.
have sid1:prl_same_index (T  _ (pidl_i2_L sr2 leij))
     (T  _ (pidl_i1_L sr2 leij)) by [].
set QQ := prl_dl_halm_compat or1 or2 sr1 sr2.
move: (prl_map2_prop3 sid1 (QQ _ Sr _ _ leij)).
simpl;  rewrite /T -/(prl_dl_hlm _ _ _ _ _ _) prl_dl_hml_invariant.  
have ->: (prl_dl_hlm_gen or1 or2 sr1 sr2 Sr (J i j)) = hlm. 
  by rewrite /hlm prl_dl_hml_invariant; aw.
rewrite -prl_dl_F_lambda_prop  -prl_dl_F_lambda_prop.
rewrite /prl_dl_F_lambda -/Si - /Sj.
move => [[fLa sLa tLa] Lap].
have sid2:prl_same_index (T' _ (pidl_i2_L sr2 leij))
     (T' _ (pidl_i1_L sr2 leij)) by [].
move:(prl_map2_prop3 sid2 (QQ _ Sr' _ _ leij)).
simpl;  rewrite /T -/(prl_dl_hlm _ _ _ _ _ _) prl_dl_hml_invariant.  
have ->: (prl_dl_hlm_gen or1 or2 sr1 sr2 Sr' (J i j)) = hlm'. 
  by rewrite /hlm' prl_dl_hml_invariant; aw.
rewrite -prl_dl_F_lambda_prop  -prl_dl_F_lambda_prop.
rewrite /prl_dl_F_lambda -/Si' - /Sj'.
move => [[fLb sLb tLb] Lbp].
have res1: V i \coP hlm by split => //; ue.
have res2: hlm' \coP V j by split => //; ue.
apply:function_exten.
+  by apply: compf_f.
+  by apply: compf_f.
+ aw; ue.
+ aw; ue.
+ aw; rewrite sLa => x xsj.
  have xs1:inc x (source (V j)) by ue.
  have xs2: inc x (source hlm) by ue.
  rewrite !compfV//.
have qa: inc (Vf hlm x) Si by Wtac.
have qb: inc (Vf (V i) (Vf hlm x)) Si' by Wtac.
have qa': inc (Vf (V j) x) Sj' by Wtac.
have qc: inc (Vf hlm' (Vf (V j) x)) Si' by Wtac; rewrite sLb; Wtac.
move/prl_limitP: qb => [pa pb pc _].
move/prl_limitP: qc => [pa' pb' pc' _].
apply/fgraph_exten => //; first ue.
have qe: psI (prl_dl2_Slambda i) = I1.
  rewrite /prl_dl2_Slambda /prl_dl_system_S_lambda.
  by case: (ixm (inc i I2)).
have qe': psI (prl_dl2_Slambda' i) = I1.
  rewrite /prl_dl2_Slambda' /prl_dl_system_S_lambda.
  by case: (ixm (inc i I2)).
move: pc';rewrite pb qe' => pc' k kI1.
have kI2: inc k (psI (prl_dl2_Slambda i)) by ue.
rewrite - (Lbp k _ kI1 qa') /prl_dl_halm_fam LgV//.
have kI3 : inc k (psI (prl_dl2_Slambda j)).
  rewrite /prl_dl2_Slambda /prl_dl_system_S_lambda.
  by case: (ixm (inc j I2)).
rewrite -(Vjp k _ kI3 xsj) - (Vip k  (Vf hlm x)  kI2 qa) /prl_dl2_ulam_fam.
rewrite ! LgV// - (Lap _ _ kI1 xsj) /prl_dl_halm_fam LgV//.
have le4: gle (psr S) (J k i) (J k j).
  rewrite Sr; apply/pidl_gleP1; split => //.
  by apply: (proj32 or1); rewrite sr1.
move: (le4); rewrite Sr -Sr' => le4'.
move:(prl_prop4 le4) =>[fkikj skikj tkikj].
move:(prl_prop4 le4') =>[fkikj' skikj' tkikj'].
move:(prl_prop0 le4) => [le4a le4b].
move: (proj43 compat_u _ le4a)  => [fui sui tui].
move: (proj43 compat_u _ le4b) => [fuj suj tuj].
have co2: Vg (psf S') (J (J k i) (J k j)) \coP Vg u (J k j) by split => //; ue.
have co3: Vg u (J k i) \coP Vg (psf S) (J (J k i) (J k j)) by split => //; ue.
have xs3:  inc (Vg x k) (source (Vg u (J k j))).
  rewrite suj; move/prl_limitP: xsj => [_ _ h _].
  move:(h k kI3); rewrite /prl_dl2_Slambda /prl_dl_system_S_lambda.
  case: (ixm (inc j I2)) => // H /=.
  rewrite /prl_dl_Elam_fam ! LgV//.
have xs4: inc (Vg x k) (source (Vg (psf S) (J (J k i) (J k j)))).
  by rewrite skikj - suj.
move:(proj44 compat_u  (J k i) (J k j) le4) => cc.
move:(f_equal (Vf ^~(Vg x k)) cc); rewrite  !compfV//.
Qed.

Lemma prl_dl2_res3
  (pl1 := projective_limit_fun S S' u)
  (pl2 := projective_limit_fun prl_dl2_limlim  prl_dl2_limlim' prl_dl2_v_fam)
  (bij1 :=  prl_dl_can_iso or1 or2 sr1 sr2 Sr)
  (bij2 := prl_dl_can_iso or1 or2 sr1 sr2 Sr'):
  [/\ bijection bij1, bijection bij2 & pl2 \co bij1  =  bij2 \co pl1].
Proof.
move:(prl_map2_prop3  psr_dl2_SrSr compat_u) => /=.
rewrite -/pl1.
set E :=  (projective_limit S); set E':= (projective_limit S').
move => [[fpl1 spl1 tpl1] pl1_prop].
have ha: prl_same_index prl_dl2_limlim prl_dl2_limlim' by [].
move: (prl_map2_prop3 ha prl_dl2_res2); simpl.
rewrite -/pl2.
set vE:= projective_limit _; set vE':= projective_limit _.
move => [[fpl2 spl2 tpl2] pl2_prop].
move:(prl_dl_canon_bijection or1 or2 sr1 sr2 Sr).
move:(prl_dl_canon_bijection or1 or2 sr1 sr2 Sr').
rewrite -/bij1 -/bij2 -/E -/E' -/vE -/vE'.
move => [bp2 sf2 tf2] [bp1 sf1 tf1].
split => //.
move:(bp2)(bp1) => [[ff1 _] _] [[ff2 _] _].
have co1: pl2 \coP bij1 by split => //; ue.
have co2: bij2 \coP pl1 by split => //; ue.
apply: function_exten;try (apply: compf_f => //);  aw; try ue.
rewrite sf1 => x xE.
have xs1: inc x (source pl1) by ue.
have xs2: inc x (source bij1) by ue.
have xs3:inc (Vf pl1 x) E' by Wtac.
have ax1:lf_axiom (prl_dl_slice2 I1 I2) (projective_limit S')
   (projective_limit (prl_dl_systemS' or1 or2 sr1 sr2 Sr')).
  by apply:prl_dl_slice_p2.
have ax2: lf_axiom (prl_dl_slice2 I1 I2) (projective_limit S)
   (projective_limit (prl_dl_systemS' or1 or2 sr1 sr2 Sr)).
  by apply:prl_dl_slice_p2.
rewrite !compfV //.
have xs4: inc (Vf bij1 x) vE by Wtac.
have xs4': inc (Vf pl2 (Vf bij1 x)) vE' by  Wtac.
have xs5: inc (Vf bij2 (Vf pl1 x)) vE' by Wtac.  
move/(prl_limitP): xs4' => [qa qb qc _].
move/(prl_limitP): xs5 => [qa' qb' qc' _].
apply: fgraph_exten => //; first ue.
rewrite qb => l /= lI2; clear qa qb qa' qb'.
move: (qc l lI2); rewrite /= LgV//prl_dl_F_lambda_prop.
move/(prl_limitP) => [ra rb  _ _].
move: (qc' l lI2); rewrite  /= LgV//prl_dl_F_lambda_prop.
move/(prl_limitP) => [ra' rb'  _ _].
apply/fgraph_exten => //; first ue.
move => i; rewrite rb /= => iI1; clear ra rb ra' rb'.
have ijI: inc (J i l) (psI S).
  rewrite - ps_substrate_r Sr.
  rewrite (proj2 (pidl_or or1 or2 sr1 sr2)); fprops.
rewrite - (pl2_prop _ _ lI2 xs4).
rewrite /bij1/bij2/prl_dl_can_iso. rewrite LfV// LfV//.
rewrite/prl_dl_slice2 /prl_dl2_v_fam ! LgV// /prl_dl_slice.
rewrite - (pl1_prop _ _ ijI xE).
have iI3: inc i (psI (prl_dl2_Slambda l)).
  rewrite /prl_dl2_Slambda /prl_dl_system_S_lambda.
  by case: (ixm (inc l I2)). 
have sl: inc (prl_dl_slice I1 x l) (projective_limit (prl_dl2_Slambda l)).
  by apply:(prl_dl_slice_p1).
move: (prl_dl2_res1 lI2) => [hax hbx].
rewrite -  (proj2 (prl_map2_prop3 hax hbx) _ _ iI3 sl).
rewrite/prl_dl2_ulam_fam/prl_dl_slice !LgV//.
Qed.

End  DoubleInverseLimit2.




Section  DoubleInverseLimit3.

Variables I L r: Set.
Variable fS: Set -> projective_system.
Hypothesis (or: preorder r)(sr: substrate r = I).

Hypothesis fSr: forall l, inc l L -> psr (fS l) = r.

Lemma prl_dl3_fSI l: inc l L -> psI (fS l) = I.
Proof. by rewrite - ps_substrate_r; move => /fSr ->. Qed.

Definition prl_dl3_or := prod_of_relation r (diagonal L).


Lemma prl_dl3_orL: preorder (diagonal L).
Proof. by move: (diagonal_osr L)=> [/order_preorder]. Qed.

Lemma prl_dl3_srL: substrate (diagonal L) = L.
Proof. by case: (diagonal_osr L). Qed.


Lemma prl_dl3_osr: preorder_on (prl_dl3_or) (I \times L).
Proof. 
split; first by apply:(order_product2_preorder or prl_dl3_orL). 
by move:(order_product2_sr1 or prl_dl3_orL); rewrite  sr prl_dl3_srL.
Qed.

Lemma prl_dl3_or_prop1 p: inc p (prl_dl3_or) ->
  [/\ pairp p, inc (P p) (I\times L), inc (Q p) (I\times L), 
     inc (J (P (P p)) (P (Q p))) r & (Q (P p)) = (Q (Q p))].
Proof.
move => h; move: (proj31(proj1 prl_dl3_osr) _ h) => pp.
move: h; rewrite - {1} pp; set x := (P p); set y := Q p.
move/prod_of_rel_P => [ha hb hc hd]. 
move/diagonal_pi_P:(hd) => [_ qq].
move:(arg1_sr hc) (arg2_sr hc) (arg1_sr hd) (arg2_sr hd).
by rewrite sr prl_dl3_srL => qa qb qc qd;split => //;apply/ setX_P.
Qed.

Definition prl_dl3_E := Lg (I\times L) (fun p => Vg (psE (fS (Q p))) (P p)).
Definition prl_dl3_f := Lg prl_dl3_or
    (fun p => Vg (psf (fS (Q (Q p)))) (J (P (P p)) (P (Q p)))).

Definition prl_dl3_systemS: projective_system.
Proof.
apply(@ProjectiveSystem prl_dl3_E (I\times L) prl_dl3_or  prl_dl3_f).
- exact (proj1 prl_dl3_osr).
- exact (proj2 prl_dl3_osr).
- rewrite /prl_dl3_E; fprops.
- by rewrite /prl_dl3_E; aw.
- rewrite /prl_dl3_f; fprops.
- by rewrite /prl_dl3_f; aw.
- move => p pp; move:( prl_dl3_or_prop1 pp) => [qa qb qc qd qe].
   rewrite/prl_dl3_f /prl_dl3_E !LgV//  qe.
   move/setX_P:qc => [_ _ qqL]; rewrite - (fSr qqL) in qd.
   by move:(ps_function_f qd); aw.
- move => i j k lij ljk.
  have lik:inc (J i k) prl_dl3_or by apply:(proj33 (proj1 prl_dl3_osr)) lij ljk.
  rewrite / prl_dl3_f ! LgV//.
  move:(prl_dl3_or_prop1 lij) (prl_dl3_or_prop1 ljk); aw.
  move => [_ ip jp lij' _] [_ _ kp ljk' ->]. move/(setX_P): kp => [_ _ qkL].
  apply: ps_compose_f => //; rewrite fSr //.
- move => p pp; rewrite /prl_dl3_f /prl_dl3_E ! LgV//; aw.
    move/setX_P: pp => [pa pb pc].
    by rewrite - ps_identity_f // - ps_substrate_r fSr // sr.
  move: prl_dl3_osr=> [qa qb]; rewrite - qb in pp; exact: (proj32 qa p pp).
Defined.  

Lemma  prl_dl3_systemS_prop: projective_system_on prl_dl3_systemS
   prl_dl3_E (I\times L) prl_dl3_or  prl_dl3_f.
Proof. by []. Qed.

Lemma prl_dl3_systemS_sr: psr prl_dl3_systemS = prod_of_relation r (diagonal L).
Proof. by []. Qed.

Let iso:= (prl_dl_can_iso or prl_dl3_orL sr prl_dl3_srL prl_dl3_systemS_sr).
Let S':= (prl_dl_systemS' or prl_dl3_orL sr prl_dl3_srL prl_dl3_systemS_sr).
Let E := Lg L(prl_dl_F_lambda or prl_dl3_orL sr prl_dl3_srL prl_dl3_systemS_sr).


Lemma prl_dl3_RHS: (projective_limit S') = productb E.
Proof.
set_extens t; [ by case/Zo_P | move => tp; apply:(Zo_i tp)].
move => i j ilj; move/diagonal_pi_P:(ilj) => [iI ea]; rewrite - ea /=.
rewrite - [Lg _ _]/(psf S') ps_identity_f // idV //.
by move/setXb_P: tp => [_ _ px]; apply: px => //; rewrite /E; aw. 
Qed.

Lemma prl_dl3_systemS_can:
  bijection_prop iso (projective_limit prl_dl3_systemS) (productb E).
Proof.
rewrite - prl_dl3_RHS.
exact: (prl_dl_canon_bijection or prl_dl3_orL sr prl_dl3_srL
                                 prl_dl3_systemS_sr).
Qed.


Definition prl_dl3_Efam i :=
  Lg L (fun l => Vg (psE (fS l)) i).
Definition prl_dl3_Ep i := productb (prl_dl3_Efam i).

Definition prl_dl3_mod x :=
  Lg I (fun i => (Lg L (fun l => Vg x (J i l)))). 

Lemma prl_dl3_mod_p1 x: inc x  (projective_limit prl_dl3_systemS) ->
  inc  (prl_dl3_mod x) (productb (Lg I prl_dl3_Ep)).
Proof.
move => /prl_limitP /= [p1 p2 p3 _].
rewrite /prl_dl3_mod; apply/setXb_P;aw; split; fprops => i iI; rewrite !LgV//.
apply/setXb_P; rewrite /prl_dl3_Efam; aw; split; fprops => j jL; rewrite !LgV//.
have pp: inc (J i j) (I \times L) by apply: setXp_i.
by move: (p3 _ pp);rewrite /prl_dl3_E LgV//; aw.
Qed.

Lemma prl_dl3_mod_inj x y:
  inc x  (projective_limit prl_dl3_systemS) ->
  inc y  (projective_limit prl_dl3_systemS) ->
   (prl_dl3_mod x)  = (prl_dl3_mod y) -> x = y.
Proof.
move => /prl_limitP /= [p1 p2 p3 _] /prl_limitP /= [q1 q2 q3 _].
rewrite /prl_dl3_mod => eq1.
apply: fgraph_exten => //; rewrite p2 // => t /setX_P [pa pb pc].
by move: (f_equal (fun z => (Vg (Vg z (P t)) (Q t))) eq1); rewrite !LgV// pa.
Qed.


Definition prl_dl3_ffam :=
  Lg r (fun ij => (ext_map_prod L (fun l => Vg (psE (fS l)) (Q ij))
                                (fun l => Vg (psE (fS l)) (P ij))
                                (fun l => (graph (Vg (psf (fS l)) ij))))).


Lemma prl_dl3_ffam_ax ij: inc ij r ->
   ext_map_prod_axioms L (fun l : Set => Vg (psE (fS l)) (Q ij))
     (fun l => Vg (psE (fS l)) (P ij))
     (fun l => graph (Vg (psf (fS l)) ij)).
Proof.
move => ijr l lL.
rewrite - (fSr lL) in ijr.
move:(ps_function_f ijr); set f:= Vg _ _; set Ej := Vg _ _; set Ei := Vg _ _.
by move => [[/corr_propc /proj33 ha hb hc] <- <-].
Qed.  


  
Lemma prl_dl3_ffam_fun ij: inc ij r ->
  function_prop (Vg prl_dl3_ffam ij) (prl_dl3_Ep (Q ij)) (prl_dl3_Ep (P ij)).
Proof.
move => ijr.
rewrite /prl_dl3_ffam LgV// /function_prop /ext_map_prod; aw.
by split=> //;apply:ext_map_prod_f; apply:prl_dl3_ffam_ax.
Qed.  

Lemma  prl_dl3_ffam_id i: inc i I ->
   Vg prl_dl3_ffam (J i i) = identity (prl_dl3_Ep i).
Proof.
move => iI.
have rii: inc (J i i) r by apply: (proj32 or); rewrite sr.
case: (prl_dl3_ffam_fun  rii); aw => ha hb hc.
apply:function_exten => //; aww; rewrite hb => x xE.
rewrite /prl_dl3_ffam LgV// idV //; aw; rewrite ext_map_prod_V; fprops; last first.
  by move:(prl_dl3_ffam_ax rii);  aw.
move: xE; rewrite /prl_dl3_Ep/prl_dl3_Efam => /setXb_P [fgx dx xv].
apply: fgraph_exten; fprops; aw; first by rewrite dx;aw.
move => l lL /=;rewrite LgV // /ext_map_prod_aux. 
have iI': inc i (psI (fS l)) by rewrite -ps_substrate_r (fSr lL) sr.
rewrite (ps_identity_f iI') -/(Vf _ _) idV //.
by move:(xv l); aw; rewrite LgV//; apply.
Qed.

Lemma  prl_dl3_ffam_comp i j k: gle r i j ->  gle r j k ->
   Vg prl_dl3_ffam (J i j) \co Vg prl_dl3_ffam (J j k) =
   Vg prl_dl3_ffam (J i k).
Proof.
move => lij ljk; move:(proj33 or _ _ _ lij ljk) => lik.
rewrite /prl_dl3_ffam  !LgV//.
have hc l: inc l L ->
   graph (Vg (psf (fS l)) (J i j)) \cfP graph (Vg (psf (fS l)) (J j k)).
  move => lL.
  have ha:  gle (psr (fS l)) i j by rewrite fSr.
  have hb:  gle (psr (fS l)) j k by rewrite fSr.
  move:(ps_function_f ha) (ps_function_f hb) => [ff sf _] [ff' _ tf].
  rewrite pr2_pair in sf; rewrite pr1_pair in tf.
  split; fprops. rewrite domain_fg // sf - tf. 
  exact: (proj33 (corr_propc (proj31 ff'))).
aw; apply:ext_map_prod_compose.
- by move: (prl_dl3_ffam_ax ljk); aw.
- by move: (prl_dl3_ffam_ax lij); aw.
- move => l lL.
  have ha:  gle (psr (fS l)) i j by rewrite fSr.
  have hb:  gle (psr (fS l)) j k  by rewrite fSr.
  rewrite -(ps_compose_f ha hb) /compose; aw; symmetry;apply:compg_composef.
  by apply: hc.
- apply: hc.
Qed.
  
      
Definition prl_dl3_systemS': projective_system.
Proof.
apply(@ProjectiveSystem (Lg I prl_dl3_Ep) I r prl_dl3_ffam).
- exact.
- exact.
- fprops.
- by aw.
- rewrite /prl_dl3_ffam; fprops.
- by rewrite /prl_dl3_ffam Lgd.
- move => i ir; move:(pr1_sr ir) (pr2_sr ir); rewrite sr => ha hb.
  rewrite LgV // LgV//; apply:(prl_dl3_ffam_fun ir).    
- by move => i j k lij ljk; apply:prl_dl3_ffam_comp.
- by move => i iI; rewrite LgV//; apply:prl_dl3_ffam_id.
Defined.

Lemma  prl_dl3_systemS'_val: projective_system_on  prl_dl3_systemS'
       (Lg I prl_dl3_Ep) I r prl_dl3_ffam.
Proof. done. Qed.

Lemma prl_dl3_res (X := (projective_limit prl_dl3_systemS))
      (Y := projective_limit prl_dl3_systemS'):
  bijection_prop (Lf prl_dl3_mod  X Y) X Y.
Proof.
saw; apply: lf_bijective.
+ move => x xX; move/setXb_P:( prl_dl3_mod_p1 xX)=> []; aw => pa pb pc.
  apply/prl_limitP; split; fprops => i j /= lij.
  move:(arg1_sr lij)(arg2_sr lij); rewrite sr => iI jI.
  rewrite /prl_dl3_mod / prl_dl3_ffam LgV// LgV// LgV//.
  move/prl_limitP: xX => [qa qb qc qd].
  rewrite (ext_map_prod_V (prl_dl3_ffam_ax lij)).
    apply:Lg_exten => l lL; rewrite/ext_map_prod_aux -/(Vf _ _).
    have ha:gle prl_dl3_or (J i l) (J j l). 
     by apply/pidl_gleP; split;  aww;apply/diagonal_pi_P.
    by rewrite (qd _ _ ha) /= /prl_dl3_f; rewrite  ! LgV//; aw.
  apply/setXf_P; split;aww => l lL; rewrite LgV//.
  have ha:= (setXp_i jI lL).
  by move: (qc (J j l) ha); rewrite /= /prl_dl3_E LgV//; aw.
+ apply prl_dl3_mod_inj.
+ move => y /prl_limitP[] /= fgy dy pa pb.
  set x := Lg (I\times L) (fun il => Vg (Vg y (P il)) (Q il)).
  exists x.
    rewrite /x;apply/prl_limitP; split; aww.
      move => il /= ilIL;  rewrite LgV//.
      move/setX_P: (ilIL) => [pp iI lL]; move:(pa _ iI); rewrite LgV//.
      rewrite /prl_dl3_E /prl_dl3_Ep LgV//.
      move/setXb_P => [qa qb ]; aw; rewrite /prl_dl3_Efam; aw => qc.
      move: (qc _ lL); rewrite LgV//.
   move => p1 p2 /= lp1p2.
   move: (prl_dl3_or_prop1 lp1p2); aw; move => [_ p1p p2p l12 qq].
   have hq: inc (Q p1) L by case/setX_P:p1p.
   move:(pb _ _ l12); rewrite /prl_dl3_f /prl_dl3_ffam !LgV//; aw.
   rewrite (ext_map_prod_V).
       by move => ->; rewrite /ext_map_prod_aux LgV// qq.
     by move:(prl_dl3_ffam_ax l12); aw.
  have hr: inc (P p2) I by case/setX_P:p2p.
  move:(pa _ hr); rewrite LgV//.
rewrite/x/prl_dl3_mod;apply: fgraph_exten; aww.
rewrite dy;move => i iI /=; rewrite LgV//.
move: (pa _ iI); rewrite LgV// => /setXb_P[].
rewrite /prl_dl3_Efam;aw => qa qb qc.
apply:fgraph_exten; aww; rewrite qb => l lL.
have ha: inc (J i l) (I \times L) by apply: setXp_i.
by rewrite ! LgV//; aw.
Qed.

End  DoubleInverseLimit3.




(**  Conditions for a projective limit to be nonempty *)

Section ProjectiveLimitNonEmpty1.

Variable S: projective_system.
Hypothesis rdr:right_directed_prop (psr S).
Hypothesis sjf: forall i, inc i (psr S) -> surjection  (Vg (psf S) i).

Definition prl_ne1_some_nonempty := 
  (exists2 i, inc i (psI S) & nonempty(Vg (psE S) i)).

Lemma prl_ne1_allE_ne: prl_ne1_some_nonempty ->
   forall i, inc i (psI S) -> nonempty(Vg (psE S) i).
Proof.
move => [i iI [x xEi]] j jI.
rewrite - ps_substrate_r in iI jI.
move:(rdr  iI jI) => [k [le1 le2]].
move: (ps_function_f le1)(ps_function_f le2) => [ff1 sf1 tf1] [ff2 sf2 tf2].
have xt: inc x (target (Vg (psf S) (J i k))) by rewrite tf1; aw.
move:(proj2 (sjf le1) _ xt); rewrite sf1; aw; move => [y ya _].
move:(Vf_target ff2); rewrite sf2 tf2;aw => h; move: (h _ ya) => yb; ex_tac.
Qed.

Lemma prl_ne1_res1: ~  prl_ne1_some_nonempty ->
  forall i, inc i (psI S) -> surjection (prl_can_fun S i).
Proof.
rewrite /prl_ne1_some_nonempty=> H i iI.
move:(prl_can_fun_fp iI) => [ff sf tf]; split => //; rewrite sf tf => y yI.
case: H; ex_tac; ex_tac.
Qed.


Lemma prl_ne1_surj_rec i j  (f := prl_can_fun S):
  gle (psr S) i j  -> surjection (f j) -> surjection  (f i).
Proof.
move => lij sa.
move:(prl_can_fun_prop lij)(sjf lij); rewrite -/f; move => [sc ->] sd.
by apply: compose_fs.
Qed.

Lemma prl_ne1_res2:
  (exists2 j, inc j (psI S) & forall i, inc i (psI S) -> gle (psr S) i j) ->
  forall i, inc i (psI S) -> surjection (prl_can_fun S i).
Proof.
move => [j jI jge].
move => i iI; move: (jge _ iI) => h; apply:(prl_ne1_surj_rec h).
move:(prl_can_fun_fp jI) => [fa sa ta]; split=> //; rewrite sa ta {i iI h}.
move => y ys.
set x := Lg (psI S) (fun i => Vf (Vg (psf S) (J i j)) y).
have xp: inc x (projective_limit S).
  rewrite /x; apply/prl_limitP; aw; split; fprops.
    move => i iI; rewrite LgV//; move: (ps_function_f (jge _ iI)); aw => - [fb sb tb];Wtac.
  move => i k leik.
  move: (arg1_sr leik) (arg2_sr leik). 
  rewrite ps_substrate_r => iI kI; rewrite ! LgV//.
  by rewrite (prl_prop3 leik (jge _ kI) ys).
exists x => //;rewrite prl_proj_ev // /x; rewrite LgV//.
by rewrite (ps_identity_f  jI) idV//.
Qed.

Lemma prl_ne1_res3 A: cofinal (psr S) A -> finite_set A ->
   forall i, inc i (psI S) -> surjection (prl_can_fun S i).
Proof.
move => [sra cfa] fa.
case: (emptyset_dichot (psI S)) => neI.
    by rewrite neI => i /in_set0.  
move:(proj33 (ps_preorder_r S)) => ot.
have HA: forall x, finite_set x -> 
         (sub x (substrate (psr S))  -> exists y, upper_bound (psr S) x y). 
  apply: finite_set_induction.
    move => _; move: neI => [y yI]; exists y => //; split.
     by rewrite ps_substrate_r.
     by move => t /in_set0.
  move => a b h1 h2; move:(h1(sub_trans (@subsetU2l _ _) h2)) => [y [ya yb]].
  have bsr := (h2 _ (setU1_1 a b)).
  move:(rdr ya bsr) => [z [za zb]]; exists z; split => //; first by order_tac.
  move => t /setU1_P [ta  | -> //]; by  exact:(ot _ _ _ (yb _ ta) za).
move: (HA _ fa sra) => [y [ya yb]].
apply:prl_ne1_res2; exists y; first by rewrite - ps_substrate_r.
rewrite - ps_substrate_r. 
move => i iI; move:(cfa _  iI) => [z /yb za] le; apply: (ot _ _ _ le za).
Qed.

Lemma prl_ne1_res4 A: cardinal A = aleph0 -> cofinal (psr S) A -> 
   exists f, [/\  function f, source f = Nat,
        forall i, natp i -> gle (psr S) (Vf f i) (Vf f (csucc i)) &
        forall i, inc i (psI S) -> exists2 n, natp n & gle (psr S) i (Vf f n) ].
Proof.
move => ha hb.
pose pp pr z :=  gle (psr S) (P pr) z /\ gle (psr S) (Q pr) z.
pose ch1 pr := choose (pp pr).
have pa pr: inc pr (coarse (substrate (psr S))) -> pp pr (ch1 pr).
   by move => /setX_P[qa qb qc]; apply: choose_pr; move:(rdr qb qc). 
have pb i j: inc i (psI S) -> inc j (psI S) ->
    gle (psr S) i (ch1 (J i j)) /\ gle (psr S) j (ch1 (J i j)).
  move => qa qb.
  have: (inc (J i j) (coarse (substrate (psr S)))).
     by rewrite ps_substrate_r; apply:setXp_i.
  by move/pa; rewrite /pp; aw.
move: (esym ha);rewrite aleph0_pr1 => /card_eqP [g [[[fg _] [_ sjg]] sg tg]].
move:(induction_defined_pr0(fun n v => ch1 (J (Vf g n) v))(Vf g \0c)).
set f := induction_defined0 _ _; move => [sf [ff _] f0 fS].
have pc n: natp n -> inc (Vf g n) (psI S). 
  move => nN; move:(proj1 hb); rewrite ps_substrate_r; apply; Wtac; ue.
have pd n: natp n -> inc (Vf f n) (psI S). 
  move:n; apply:Nat_induction; first by rewrite f0; apply: pc; fprops.
  move => n nN hr; rewrite (fS _ nN).
  by move:(arg2_sr (proj1 (pb _ _ (pc _ nN) hr))); rewrite ps_substrate_r.
exists f; split => //.
  move => i iN; rewrite (fS _ iN);exact:(proj2 (pb _ _ (pc _ iN) (pd _ iN))).
move => i iI.
have isr:inc i (substrate (psr S)) by rewrite ps_substrate_r.
move:(proj2 hb i isr) => [y yA leiy]; rewrite sg tg in sjg.
move:(sjg _ yA) => [n nN yv].
move:(arg2_sr leiy); rewrite ps_substrate_r => yI.
exists (csucc n);  first by apply: (NS_succ nN).
move:(proj1 (pb y (Vf f n) yI (pd _ nN))); rewrite (fS _ nN) - yv.
apply: (proj33 (ps_preorder_r S) _ _ _ leiy).
Qed.


Lemma prl_ne1_res5: (exists2 A, countable_set A & cofinal(psr S) A ) ->
  forall i, inc i (psI S) -> surjection (prl_can_fun S i).
Proof.
move => [A countA cfA].
case:(countable_finite_or_N countA) => cardA.
  by apply: (prl_ne1_res3 cfA cardA).
move: (prl_ne1_res4 cardA cfA) => [f [ff sf  fp1 fp2]].
have otr := proj33 (ps_preorder_r S).
have fiI i:  natp i -> inc (Vf f i) (psI S).
  by move => iN; move:(arg1_sr (fp1 _ iN)); rewrite ps_substrate_r.
have fp3 i j : natp i -> natp j -> i <=c j -> gle (psr S) (Vf f i) (Vf f j).
   move => iN jN leij.
   rewrite - (cdiff_pr leij). move:(NS_diff i jN); move:(j -c i).
   clear jN leij; apply:Nat_induction.
       rewrite (csum0r (CS_nat iN)); apply: (proj32 (ps_preorder_r S)).
       rewrite ps_substrate_r; apply:(fiI _ iN).
    move => n nN hr; rewrite  (csum_nS _ nN).
    exact: (otr _ _ _ hr (fp1 _ (NS_sum iN nN))).
move => i iI; move: (fp2 _ iI) => [n nN ha].
apply:(prl_ne1_surj_rec ha) ; clear i iI ha.
move:(prl_can_fun_fp (fiI _ nN)); set fn := (prl_can_fun S (Vf f n)).
move=> [fbf sfn tfn]; split => //; rewrite sfn tfn => [y yIEn].
pose nexty i y z := inc z (Vg (psE S) (Vf f (csucc (n +c i)))) /\
  Vf (Vg (psf S) (J (Vf f (n +c i)) (Vf f (csucc (n +c i))))) z = y.
pose ch2 i y  := choose (nexty i y).
have pa i t: natp i -> inc t (Vg (psE S) (Vf f (n +c i)))   ->
   nexty i t (ch2 i t).
   move =>  iN tE. 
   move:(fp1 _ (NS_sum nN iN)) => le1.
   move: (sjf  le1) (ps_function_f le1) => [fg sg][_ sog tag].
   move: sg; rewrite  sog tag; aw => h; move:(h t tE) => [x xa xb].
   by apply: choose_pr; exists x.
move:(induction_defined_pr0(fun n v => ch2 n v) y).
set g := induction_defined0 _ _; move => [sg [fg _] g0 gS].
have  np0 := (csum0r (CS_nat nN)).
have pb i: natp i -> inc (Vf g i) (Vg (psE S) (Vf f (n +c i))).
  move: i;apply: Nat_induction; first by rewrite np0 g0.
  move => i iN hr.
  rewrite (gS _ iN);  rewrite (csum_nS _ iN); exact:(proj1 (pa _ _ iN hr)).  
have pc i: natp i ->
     Vf (Vg (psf S) (J (Vf f (n +c i)) (Vf f (csucc (n +c i)))))
        (Vf g (csucc i)) = Vf g i.              
    move => iN; rewrite (gS _ iN); exact:(proj2 (pa _ _ iN (pb _ iN))).
pose pp3 j i := natp i /\ gle (psr S) j (Vf f (n +c i)).
pose ch3 j := choose (pp3 j).
have ch3p i: inc i (psI S) -> pp3 i (ch3 i).
  move => iI; rewrite /ch3;apply: choose_pr.
  move: (fp2 _ iI) => [j jN] leab; case: (NleT_ee jN nN) => lea.
     exists \0c; split; fprops; rewrite np0.
     exact:(otr _ _ _ leab (fp3 _ _ jN nN lea)).
  move:(cdiff_pr lea) => leb; exists (j -c n); split => //; fprops; ue.
pose xi i := Vf  (Vg (psf S) (J i (Vf f (n +c (ch3 i))))) (Vf g (ch3 i)).
have xiEi i: inc i (psI S) -> inc (xi i) (Vg (psE S) i).
  move => iI.
  move: (ch3p _ iI) => [qa qb].
  move:(ps_function_f qb); rewrite /xi; aw; set mf := (Vg (psf S) _).
  by move => [fm sm tm]; Wtac; rewrite sm; apply: pb.
have Ha p k : natp k -> p <=c k -> 
  Vf g p = Vf (Vg (psf S) (J (Vf f (n +c p)) (Vf f (n +c k)))) (Vf g k).
  move => kN lpk;  move: (NS_le_nat lpk kN) => pN.
   rewrite - (cdiff_pr lpk);  move:(NS_diff p kN); move:(k -c p).
   clear k kN lpk; apply:Nat_induction.
     have qq:inc (Vf f (n +c p)) (psI S) by apply: (fiI _ (NS_sum nN pN)).
     by rewrite (csum0r (CS_nat pN)) (prl_prop5 qq (pb _ pN)).
   move=> k kN h; move: (NS_sum pN kN) => pkN.
   rewrite (csum_nS _ kN) (gS _ pkN) h (csum_nS _ pkN).
   move: (pa _ _ pkN (pb  _ pkN)) => []; set u := ch2 _ _ => uE <-.
   apply:prl_prop3 uE.
      by apply: fp3; fprops; rewrite csumA; apply:csum_M0le; fprops.
    by  apply: fp3; fprops.
have Hb i k p: natp k -> p  <=c k -> gle (psr S) i (Vf f (n +c p)) ->
             Vf (Vg (psf S) (J i (Vf f (n +c p)))) (Vf g p) =
             Vf (Vg (psf S) (J i (Vf f (n +c k)))) (Vf g k).
    move => kN lpk lei1; move: (NS_le_nat lpk kN) => pN.
    have le2: gle (psr S) (Vf f (n +c p)) (Vf f (n +c k)).
      by apply:(fp3 _ _(NS_sum nN pN) (NS_sum nN kN)); apply:csum_Meqle.
    by rewrite - (prl_prop3 lei1 le2 (pb _ kN)) - (Ha _ _ kN lpk).
have xii i j: inc i (psI S) -> natp j ->  gle (psr S) i (Vf f (n +c j)) ->
   xi i = Vf  (Vg (psf S) (J i (Vf f (n +c j)))) (Vf g j).
  move => iI jN ha.
  move:  (ch3p _ iI) => [qa qb]; rewrite /xi.
  set k := cmax j (ch3 i).
  move: (Nmax_p1 jN qa);rewrite -/k; move => [kN kl1 kl2].
  by rewrite (Hb _ _ _ kN kl1 ha) (Hb _ _ _ kN kl2 qb).
pose x := Lg (psI S) xi.
suff: inc x (projective_limit S). 
   move => xl; exists x => //; move : (fiI _ nN) => ha.
   rewrite (prl_proj_ev ha xl) /x LgV//.
   have ll: gle (psr S) (Vf f n) (Vf f n).
     by apply: (proj32 (ps_preorder_r S)); rewrite ps_substrate_r;apply: fiI.
   move:(xii _ _ ha NS0); rewrite np0 => h.
   by rewrite (h ll) (prl_prop5 ha) => //; move: (pb _ NS0); rewrite np0.
rewrite /x;apply/prl_limitP; split.
- fprops.
- by aw.
- move => i iI; rewrite LgV//; apply:(xiEi _ iI).
- move => i j leij.
  move:(prl_prop0 leij) => [iI jI].
  move: (ch3p _ jI) => [chN lejc].
  have leic:= (otr _ _ _ leij lejc).
  by rewrite !LgV // (xii _ _ iI chN leic) (prl_prop3 leij lejc) //; apply: pb.
Qed.

  
End ProjectiveLimitNonEmpty1.


(* Mettre ailleurs *)

Lemma finite_U2 x y: finite_set x -> finite_set y -> finite_set (x\cup y).
Proof.
move=> /card_finite_setP ns1 /card_finite_setP ns2; apply/card_finite_setP.
move:  (csum2_pr6 x y); rewrite - csum2cl - csum2cr => h.
exact:(NS_le_nat h (NS_sum ns1 ns2)).
Qed.

Lemma setIf_alt I f:
  (intersectionf I f = intersection (range (Lg I f))).
Proof.
rewrite - setIb_alt; fprops; rewrite /intersectionb; aw.
apply:setIf_exten => i iI; rewrite LgV//.
Qed.

Lemma nonempty_range I f: nonempty I -> nonempty (range (Lg I f)).
Proof.  move => [i iI]; exists (f i); apply /Lg_range_P; ex_tac. Qed.

Section ProjectiveLimitNonEmpty2.

Variable S: projective_system.
Hypothesis rdr: right_directed_prop (psr S).
  
Definition prl_ne2_res_RHS i := 
  intersectionf  (Zo (psI S) (gle (psr S) i))
                 (fun j =>  (Imf (Vg (psf S) (J i j)))).
Definition prl_ne2_res_a:=
  forall i, inc i (psI S) -> Imf (prl_can_fun S i) = prl_ne2_res_RHS i.

Lemma prl_ne2_intP i j:
  inc j (Zo (psI S) (gle (psr S) i)) <-> (gle (psr S) i j).
Proof.
split; first by case/Zo_P.
move =>h;apply:Zo_i=> //; rewrite - ps_substrate_r;exact (arg2_sr h).
Qed.


Lemma prl_ne2_int_i i: inc i (psI S) -> inc i (Zo (psI S) (gle (psr S) i)).
Proof.
by move => ii; apply/Zo_P; split => //; apply: (prl_prop1).
Qed.
  
Lemma prl_ne2_prop_trivial:
   (exists2 i, inc i (psI S) & Vg (psE S) i = emptyset) ->
   prl_ne2_res_a.
Proof.
move => [j jI Ee] i iI.
move: (prl_can_fun_fp iI) => [ff sf tf].
set_extens t.
  move/(Imf_P ff); rewrite sf; move => [u /prl_limitP [_ _ ok _] _].
  by move:(ok _ jI); rewrite Ee => /in_set0.
move:(iI) (jI); rewrite - ps_substrate_r => ir jr.
move:(rdr ir jr) => [k [leik lejk]].
move:(prl_prop4 lejk) => [fjk sjk tjk]; rewrite Ee in tjk.
move: (empty_function_p2 fjk tjk); rewrite sjk => se.
move:(prl_prop4 leik) => [fik sik tik].
move/ prl_ne2_intP: leik => kZ ti;move:(setIf_hi ti kZ) => /(Imf_P fik).
by rewrite sik se; move => [u /in_set0].
Qed.

  
Variable FS_fam: Set.

Hypothesis FS_fgraph: fgraph FS_fam.
Hypothesis FS_domain: domain FS_fam = psI S.
Hypothesis FS_range:
  forall i, inc i (psI S) -> sub (Vg FS_fam i) (\Po (Vg (psE S) i)).
Hypothesis FS_whole:
  forall i, inc i (psI S) -> inc  (Vg (psE S) i)(Vg FS_fam i).
Hypothesis FS_inter:
  forall i A, inc i (psI S) -> sub A (Vg FS_fam i) -> nonempty A ->
              inc (intersection A)(Vg FS_fam i).

Definition prl_ne1_condii i:=
  forall F, sub F (Vg FS_fam i) -> nonempty F ->
            (forall A, sub A F -> finite_set A -> nonempty A ->
                       nonempty (intersection A)) ->
            nonempty (intersection F).
Definition prl_ne1_condii' i:=
  forall F, sub F (Vg FS_fam i) -> nonempty F ->
            ~(inc emptyset F) ->
            (forall x y, inc x F -> inc y F ->
                         exists z, [/\ inc z F, sub z x & sub z y]) ->
            nonempty (intersection F).

Lemma prl_ne2_prop1 i: inc i (psI S) ->
   (prl_ne1_condii i <-> prl_ne1_condii' i).
Proof.
move => iI.
split => hb.
  move=> F fa fb fc fd; apply:hb => // A AF fsA /nonemptyP neA.
  have hc: forall B, finite_set B -> sub B F ->
                   B = emptyset \/ exists2 z, inc z F & sub z (intersection B).
    apply: finite_set_induction; first by move => _; left.
    move => a b h1 h2; right.
    have bu:= (setU1_1 a b); have bF := (h2 _ bu).
    have be: nonempty (a +s1 b) by ex_tac.
    case:(h1 (sub_trans (@subsetU2l _ _) h2)) => h3.
      by rewrite h3 set0_U2 setI_1; exists b.
    move: h3 =>[z zF zi1]; move: (fd _ _ bF zF) => [t [tf ta tb]]; ex_tac.
    move => x xt; apply/(setI_P be) => y /setU1_P; case => hc.
      exact:(setI_hi (zi1 _ (tb _ xt)) hc).
    by rewrite hc; apply: ta.
  case: (hc _ fsA AF) => // [] [z zF zi].
  case: (emptyset_dichot z) => ze; first by case:fc; ue.
  by move:ze =>[zz ziz]; exists zz; apply: zi.
move => F fa fb fc.
set G := fun_image(Zo (\Po F) (fun z => finite_set z /\ nonempty z))
  intersection.
have pg1 A: finite_set A -> nonempty A -> sub A F -> inc (intersection A) G.
  move => pa pb pc; apply/funI_P; exists A => //; apply/Zo_P; split => //.
  by apply /setP_P.
have pg2: sub F G. 
  move => t tf; rewrite - (setI_1 t); apply: pg1.
  - by apply: set1_finite.
  - fprops.
  - by apply: set1_sub.
have neG: nonempty G by case:fb => [x xf]; exists x; apply: pg2.
suff: nonempty (intersection G).
  by move => [x /(setI_P neG) xp]; exists x; apply/(setI_P fb) => t /pg2/xp.
apply:hb.
- move => t /funI_P [z /Zo_P[/setP_P zF] [fz nez] ->].
  exact:(FS_inter iI (sub_trans zF fa) nez).
- done.
- move => /funI_P [z /Zo_P[/setP_P zF] [fz nez] xv].
  by move/nonemptyP: (fc _ zF fz nez); rewrite xv.
- move => x y /funI_P[xa /Zo_P[/setP_P xF] [fx nex] xv]
            /funI_P[ya /Zo_P[/setP_P yF] [fy ney] yv].
  have ne1: nonempty (xa \cup ya) by case:nex => [a ax]; exists a; fprops.
  set z := intersection(xa \cup ya); exists z; split => //.
  + by apply: pg1; [ apply: finite_U2 |  |  apply:setU2_12S].
  + rewrite xv;move => t /(setI_P ne1) h; apply/(setI_P nex) => k ka.
    apply:h; fprops.
  + rewrite yv;move => t /(setI_P ne1) h; apply/(setI_P ney) => k ka.
    apply:h; fprops.
Qed.

Definition pr1_ne2_hyp3_aux x a b:=
  inc (Vfi1 (Vg (psf S) (J a b)) x) (Vg FS_fam b).

Definition  pr1_ne2_hyp3_plain:= forall a b  x,
  gle (psr S) a b ->  inc x (Vg (psE S) a)  ->  pr1_ne2_hyp3_aux x a b.

Definition  pr1_ne2_hyp3_weak:= forall a M,
  inc a (psI S) -> inc M (Vg FS_fam a) -> nonempty M ->
  exists2 x, inc x M & forall b, gle (psr S) a b -> pr1_ne2_hyp3_aux x a b.

Lemma pr1_ne2_hyp3_weak_prop:  pr1_ne2_hyp3_plain -> pr1_ne2_hyp3_weak.
Proof.
move => hp a M aI Mb [x xM]; exists x => // b leab.
by apply:hp => //; move: (FS_range  aI) => h; move /setP_P:(h _ Mb); apply.
Qed.

Hypothesis FS_prop_iv:
  forall i j M,  gle (psr S) i j ->  inc M (Vg FS_fam j) ->
              inc (Vfs (Vg (psf S) (J i j)) M) (Vg FS_fam i).


Hypothesis prl_ne2_ne: forall i, inc i (psI S) -> nonempty (Vg (psE S) i).

Lemma prl_ne2_im_of_id i: inc i (psI S) ->
   (Imf (Vg (psf S) (J i i))) = Vg (psE S) i.
Proof.
move => iI.
move:(identity_f (Vg (psE S) i)) => idp.
rewrite (ps_identity_f iI); set_extens t.
  move/(Imf_P idp); rewrite identity_s; move => [u ua ->]; rewrite idV//.
move => tp; apply/(Imf_P idp); rewrite identity_s; ex_tac; rewrite idV //.
Qed.


Lemma prl_ne2_res4b i: inc i (psI S) ->  prl_ne1_condii' i ->
  nonempty (prl_ne2_res_RHS i).
Proof.
move => iI ha.
rewrite /prl_ne2_res_RHS setIf_alt.
have hd: forall j,  gle (psr S) i j ->
   nonempty (Imf (Vg (psf S) (J i j))).
  move => j leij.
  move:(prl_prop0 leij) =>[_ jI].
  move: (prl_prop4 leij) => [ff sf tf].
  move: (prl_ne2_ne jI) => [x xe].  
  exists (Vf (Vg (psf S) (J i j)) x); apply/(Imf_P ff).
  rewrite sf; ex_tac.
have sub_rec j k: gle (psr S) i j -> gle (psr S) j k ->
  sub (Imf (Vg (psf S) (J i k)))  (Imf (Vg (psf S) (J i j))).
  move => lij ljk. 
  move: (proj33 (ps_preorder_r  S)_ _ _ lij ljk) => lik.
  move:(prl_prop4 lik) => [fik sik tik].
  move:(prl_prop4 ljk) => [fjk sjk tjk].
  move:(prl_prop4 lij) => [fij sij tij].
  move => t /(Imf_P fik); rewrite sik; move => [u ue ->].
  apply  /(Imf_P fij); rewrite sij -(prl_prop3 lij ljk ue).
  exists (Vf (Vg (psf S) (J j k)) u) => //; Wtac.
apply: ha.
- move => t /Lg_range_P [j /Zo_P[jI lij] ->]; apply:(FS_prop_iv lij).
  by move:(prl_prop4 lij) => [ff -> tf]; apply: FS_whole.
- exists (Vg (psE S) i); apply/Lg_range_P; exists i.
    apply:(prl_ne2_int_i iI).
  by rewrite prl_ne2_im_of_id.
- move => /Lg_range_P [ j /Zo_P[jI lij]] => be.
  by move:(hd _ lij); rewrite - be => /nonemptyP.
- move => x y /Lg_range_P [j1 /Zo_P[j1I leij1] ->].
  move => /Lg_range_P [j2 /Zo_P[j2I leij2] ->].
  move:(rdr (arg2_sr leij1) (arg2_sr leij2)) =>[k [lej1k lej2k]].
  exists (Imf (Vg (psf S) (J i k))); split.
    apply/Lg_range_P; exists k => //.
    apply/prl_ne2_intP=> //; exact:(proj33 (ps_preorder_r  S)_ _ _ leij1 lej1k).
  by apply: sub_rec.
  by apply: sub_rec.
Qed.

Lemma prl_ne2_nonempty_bis:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  prl_ne2_res_a ->
  nonempty (projective_limit S).
Proof.
move => ha hb.
case:(emptyset_dichot (psI S)) => ine.
     rewrite (prl_trivial ine); apply: set1_ne.
move:ine => [i iI]; move: (hb i iI) => hc.
suff: nonempty (Imf (prl_can_fun S i)).
  move: (prl_can_fun_fp iI) => [ff sf tf].
  move => [x /(Imf_P ff) [u]]; rewrite sf => uE _; ex_tac.
rewrite hc;apply:(prl_ne2_res4b iI (ha _ iI)).
Qed.

Definition prl_ne2_sigma :=
  Zo (productb  FS_fam) (fun A =>
      (forall i, inc i (psI S) -> nonempty (Vg A i)) /\
      (forall i j, gle (psr S) i j ->
                   sub (Vfs (Vg (psf S) (J i j)) (Vg A j)) (Vg A i))).

Lemma prl_ne2_sigma_ne: nonempty prl_ne2_sigma.
Proof.
exists (psE S); apply/Zo_P; split.
  apply/setXb_P; split; [ exact: (ps_fgraph_E) | rewrite ps_domain_E // | ].
  by rewrite FS_domain => i iI; apply: FS_whole.
split => // i j lij; move: (ps_function_f lij); aw; move => [qa qb <-].
apply: (fun_image_Starget1 qa).
Qed.
  
Definition prl_ne2_sigma_le A A' :=
  forall i, inc i (psI S) -> sub (Vg A' i) (Vg A i).

Definition prl_ne2_sigma_order := graph_on prl_ne2_sigma_le prl_ne2_sigma.

Lemma prl_ne2_sigma_osr: order_on prl_ne2_sigma_order prl_ne2_sigma.
Proof.
have ha u: inc u prl_ne2_sigma -> prl_ne2_sigma_le u u.
  move => _ i _; fprops.
have hb:=(graph_on_sr ha).
split => //;apply: order_from_rel1 => //.
   move => j i k pa pb u ui; exact:(sub_trans (pb _ ui) (pa _ ui)). 
move => u v /Zo_P[ /setXb_P [fga da _] _] /Zo_P[ /setXb_P [fgb db _] _].
move => luv lvu; apply:fgraph_exten => //; rewrite da //.
rewrite FS_domain => i iI; apply: (extensionality (lvu _ iI) (luv _ iI)).
Qed.

Lemma prl_ne2_sigma_inductive:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  inductive prl_ne2_sigma_order.
Proof.
move => H.
move: prl_ne2_sigma_osr =>[or sr].
move => L; rewrite sr => slS toL.
case: (emptyset_dichot L) => Lne.
   move:(prl_ne2_sigma_ne) => [w we]; exists w; split => //.
     by rewrite sr.
   by rewrite Lne;move =>  x /in_set0.
set x := Lg (psI S) (fun i => (intersectionf L (fun z => (Vg z i)))).
have Hb i:  inc i (psI S) -> sub (range (Lg L (Vg^~ i))) (Vg FS_fam i).
  move => iI  t/ Lg_range_P [l lL ->].
  move: (slS _ lL) => /Zo_P [/setXb_P[_ _ hb] _]; apply: hb; ue.
have Ha i: nonempty (range (Lg L (Vg^~ i))) by apply:nonempty_range.
have xs: inc x prl_ne2_sigma.
  rewrite /x;apply/Zo_P; split.
    apply/setXb_P; split; aw; fprops; rewrite FS_domain => i iI; rewrite LgV//.
    rewrite setIf_alt; apply: (FS_inter iI (Hb _ iI) (Ha i)).
  split.
    move => i iI; rewrite LgV//.
    rewrite setIf_alt; apply: ((H _ iI) _ (Hb _ iI) (Ha i)).
      move/Lg_range_P => [t ta  ee].
      move: (slS _ ta) => /Zo_P [/setXb_P[_ _ hb]  [qa _]].
      by move: (qa _ iI); rewrite - ee => /nonemptyP. 
    move => a b /Lg_range_P [u ua ub] /Lg_range_P [v va vb].
    rewrite ub vb.
    move: prl_ne2_sigma_osr => [qa qb].
    have qc:sub L (substrate prl_ne2_sigma_order)  by rewrite qb.
    move: (proj2 toL u v); rewrite (iorder_sr qa qc) => qd.
    case: (qd ua va) => /iorder_gle1 /graph_on_P1 [_ _ h]; move: (h _ iI) => k.
      by exists (Vg v i); split => //; apply/Lg_range_P;exists v.
    by exists (Vg u i); split => //; apply/Lg_range_P;exists u.
  move => i j lij.
  move: (arg1_sr lij) (arg2_sr lij); rewrite ps_substrate_r => iI jI.
  case:(ps_function_f lij); aw => [ff sf tf].
  have ha:sub (intersectionf L (Vg^~ j)) (source (Vg (psf S) (J i j))).
     rewrite sf => t/(setIf_P _ Lne) w.
     move: Lne => [l lL]; move: (w l lL);aw.
     have /(Hb _ jI) hd: inc (Vg l j) (range (Lg L (Vg^~ j))).
       apply/Lg_range_P; ex_tac.
     move:((FS_range jI) _ hd) => /setP_P; apply.
  move => t /(Vf_image_P ff); rewrite LgV//  => hc; move: (hc ha)=> [u ui ->] {hc}.
  rewrite LgV//; apply/(setIf_P _ Lne) => l lL.
  move/(setIf_P _ Lne): ui => h; move: (h _ lL) => up {h}. 
  move:(slS _ lL) => /Zo_P [qa [_ qb]]; apply: (qb _ _ lij). 
  apply/(Vf_image_P ff); last by ex_tac.
  move/setXb_P:qa => [_ _]; rewrite FS_domain  sf=> h; move: (h _ jI) => hc.
  by move /setP_P:(FS_range jI  hc).
exists x; split; first by rewrite sr.
move => y yL;  apply/graph_on_P1;split => //; first by apply:slS.
by move => i iI; rewrite /x LgV// => t /(setIf_P _ Lne); apply.
Qed.


Lemma prl_ne2_sigma_maximal_prop1 A:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  maximal prl_ne2_sigma_order A ->
  (forall i j, gle (psr S) i j -> (Vg A i)
                      = Vfs (Vg (psf S) (J i j)) (Vg A j)).
Proof.
move: prl_ne2_sigma_osr =>[or sr] H.
move => []; rewrite sr => As amax.
move/Zo_P:(As) => [ /setXb_P [fgA dA rA] [Ap1 Ap2]]. 
have Hd i: inc i (psI S) -> sub (Vg A i) (Vg (psE S) i).
  move => iI; apply/setP_P; apply:(FS_range iI); apply: rA; ue.
pose inta i:= Zo (psI S) (fun j => gle (psr S) i j).
pose II i j := Vfs (Vg (psf S) (J i j)) (Vg A j).
pose B := Lg (psI S) (fun i => intersectionf (inta i) (II i)).
pose rri i := range (Lg (inta i) (II i)).
have Ha i:inc i (psI S) ->  nonempty (inta i).
  by move => iI; exists i; apply/Zo_P; split => //; apply: prl_prop1.
have Hb i: inc i (psI S) -> nonempty (rri i).
   move => iI;apply: (nonempty_range _ (Ha i iI)).
have ra i: inc i (psI S) -> sub (rri i)  (Vg FS_fam i).
  move => iI t /Lg_range_P [j /Zo_P [jI leij] ->].
  apply:(FS_prop_iv leij); apply: rA; ue.
have rb: inc B (productb FS_fam).
rewrite/B; apply/setXb_P; split; aww; rewrite FS_domain.
  move=> i iI;rewrite LgV //setIf_alt; apply:(FS_inter iI (ra _ iI) (Hb _ iI)).
have rc i j k: gle (psr S) i j ->  gle (psr S) j k ->  sub (II i k) (II i j). 
  move => lij ljk.
  rewrite /II - (ps_compose_f lij ljk).
  case: (prl_prop4 ljk) => fjk sjk tjk.
  move: (prl_prop2 lij ljk) => coP.
  move: (arg2_sr ljk); rewrite ps_substrate_r => /Hd hb. 
  move => t/(Vf_image_P (compf_f coP));aw; rewrite sjk => ha.
  move:(ha hb) => [u uak ->]; rewrite compfV//; last by  rewrite sjk; apply: hb.
  case: (prl_prop4 lij) => fij sij tij.
  move: (arg1_sr ljk); rewrite ps_substrate_r => /Hd; rewrite - sij => hd.
  apply/(Vf_image_P fij hd);exists (Vf (Vg (psf S) (J j k)) u) => //.
  apply:(Ap2 _ _ ljk); apply/(Vf_image_P fjk); [ by rewrite sjk | ex_tac].
have rd i: inc i (psI S) -> nonempty (Vg B i).
  rewrite /B;move => iI; rewrite LgV//setIf_alt.
  apply: (H _ iI _ (ra _ iI) (Hb _ iI)).
    move/Lg_range_P => [j /Zo_P [jI leij]] se.
    case: (ps_function_f leij); aw => ff sf _.
    move: (Ap1 _ jI) => [x xa].
    move:(Hd _  jI); rewrite - sf => qa.
    have /in_set0 //: inc (Vf  (Vg (psf S) (J i j)) x) emptyset.
    rewrite se; apply/(Vf_image_P ff qa); ex_tac.
  move=> x y /Lg_range_P [j /Zo_P [jI lij] ->] /Lg_range_P[k /Zo_P [kI lik] ->].
  move:(rdr (arg2_sr lij) (arg2_sr lik)) => [l [l1 l2]].
  exists  (II i l); split; try apply: rc => //.
  apply/Lg_range_P; exists l => //; apply /Zo_P; split => //.
    by move: (arg2_sr l1); rewrite - ps_substrate_r.
  apply: (proj33 (ps_preorder_r S) _ _ _ lij l1).
have BS_sigma: inc B prl_ne2_sigma.
  apply/Zo_P; split=> //; split => // i j lij.
  move: (prl_prop0 lij) => [iI jI].
  have ->: Vg B i = intersectionf (inta j) (II i).
    rewrite /B LgV//; set_extens t.
      move=> /(setIf_P _ (Ha _ iI)) => hb.
      apply/(setIf_P _ (Ha _ jI)) => k/Zo_P[ja jb]; apply: hb.
      by apply/Zo_P; split=> //;apply: (proj33 (ps_preorder_r S) _ _ _ lij jb).
    move=> /(setIf_P _ (Ha _ jI)) => hb.
    apply/(setIf_P _ (Ha _ iI)) =>  k /Zo_P[ kI lik].
    move: (rdr (arg2_sr lij) (arg2_sr lik)) => [l [l1 l2]].
    have /hb la: inc l (inta j).
       apply/Zo_P; split => //; rewrite - ps_substrate_r; apply: (arg2_sr l1).
    exact:((rc _ _ _ lik l2) _ la).
    case: (prl_prop4 lij) => fij sij tij.
    have ha: sub (Vg B j) (source (Vg (psf S) (J i j))). 
      rewrite sij; move/setXb_P:rb => [qa qb]; rewrite FS_domain => h.
      apply/setP_P;apply:(FS_range jI); exact:(h _ jI).
    move => t /(Vf_image_P fij ha) [u ux -> ].
    move: ux; rewrite/B LgV// => /(setIf_P _ (Ha _ jI)) => hb.
    apply/(setIf_P _ (Ha _ jI)) => [k kk]; move/Zo_P: (kk) => [kI ljk].
    case: (prl_prop4 ljk) => fjk sjk tjk.
    have hc: sub (Vg A k) (source (Vg (psf S) (J j k))) by rewrite sjk; fprops.
    move/(Vf_image_P fjk hc):(hb _ kk) => [v vA ->].
    rewrite (prl_prop3 lij ljk (Hd _ kI _ vA)).
    case: (ps_function_f (proj33 (ps_preorder_r S) _ _ _ lij ljk)); aw.
    move => fik sik tik.
    apply/(Vf_image_P fik); [ rewrite sik ; fprops | ex_tac].
have cp1: gle prl_ne2_sigma_order A B.
  apply/graph_on_P1; split => // i iI; rewrite /B LgV// => t tI.
  have iii: inc i (inta i) by apply/Zo_P; split => //; apply: prl_prop1.
  have ff: function (identity (Vg (psE S) i)) by apply: identity_f.
  move:(Hd _ iI) => sb; move:(sb); rewrite -(identity_s (Vg (psE S) i)) => sa.
  move:(ps_identity_f iI) => id.
  move: (setIf_hi tI iii);rewrite /II id => /(Vf_image_P ff sa).
  by move => [u ua ->]; rewrite idV//; apply: sb.
move => i j lij.
move:(prl_prop0 lij) => [iI jI].
have ji: inc j (inta i) by apply/Zo_P.
apply: extensionality; last by apply: Ap2.
rewrite - {1} (amax _ cp1) /B LgV// => t tI. exact :(setIf_hi tI ji).
Qed.



Lemma prl_ne2_sigma_maximal_prop2 A:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  pr1_ne2_hyp3_weak ->
  maximal prl_ne2_sigma_order A ->
  (forall i, inc i (psI S) -> singletonp (Vg A i)).
Proof.
move => Hi Hii mA i iI.
move: prl_ne2_sigma_osr =>[or sr].
move: (mA) => []; rewrite sr => As amax.
move/Zo_P:(As) => [/setXb_P[dgA dA vA] [pA qA]].
rewrite FS_domain in vA.
move:(Hii i (Vg A i) iI (vA _ iI) (pA _ iI)) => [xi xia xib'].
pose II j  := (Vfi1 (Vg (psf S) (J i j)) xi).
have xib: forall j, gle (psr S) i j -> inc (II j) (Vg FS_fam j).
   by move: xib'; rewrite /pr1_ne2_hyp3_aux. 
set B := Lg (psI S)(fun j => Yo (gle (psr S) i j)(Vg A j \cap (II j)) (Vg A j)).
have ra: inc B (productb FS_fam).
  rewrite/B;apply/setXb_P; rewrite FS_domain;split; aww => j jI.
  rewrite LgV//.
  move: (vA _ jI) => ha;  Ytac hh => //; apply: (FS_inter jI).
     move => t /set2_P; case => ->; fprops.
  apply: set2_ne.   
have Ha j : gle (psr S) i j -> forall x, inc x (II j) <->
                   inc x (Vg (psE S) j) /\ xi = Vf (Vg (psf S) (J i j)) x. 
  move => lij x.
  case: (ps_function_f lij); aw => ff sf tf.
  by rewrite /II; move:(iim_fun_set1_P xi ff); rewrite sf. 
have rb: (forall j, inc j (psI S) -> nonempty (Vg B j)).
   rewrite /B;move => j jI; rewrite LgV//; Ytac lij; last by apply: pA.
   move:(xia); rewrite (prl_ne2_sigma_maximal_prop1  Hi mA lij).
   case: (ps_function_f lij); aw => ff sf tf.
   have hd: sub (Vg A j) (Vg (psE S) j).
     by apply/setP_P; apply:(FS_range jI); apply:vA.
   have hc: sub (Vg A j) (source (Vg (psf S) (J i j))) by ue.
   move /(Vf_image_P ff hc) => [u ua ub]; exists u; apply/setI2_P; split => //.
   by apply/(Ha _ lij); split => //; apply: hd.
have BS_sigma: inc B prl_ne2_sigma.
  apply/Zo_P; split=> //; split => // j k lejk.
  move:(prl_prop0 lejk) => [jI kI].
  rewrite/B ! LgV//.
  case: (ps_function_f lejk); aw => fjk sjk tjk.
  have hd: sub (Vg A k) (source (Vg (psf S) (J j k))).
    by rewrite sjk; apply/setP_P; apply:(FS_range kI); apply:vA.
  case: (p_or_not_p (gle (psr S) i j)) => leij; Ytac0.
    move:(proj33 (ps_preorder_r S) _ _ _ leij lejk) => leik.
    Ytac0.
    have ha: sub (Vg A k \cap II k) (source (Vg (psf S) (J j k))). 
       apply: (sub_trans (@setI2_1 (Vg A k) (II k)) hd).
    move => t /(Vf_image_P fjk ha) [u /setI2_P [ua ub] ->].
    apply/setI2_P; split.
      apply: (qA _ _ lejk); apply/(Vf_image_P fjk hd); ex_tac.
    move/(Ha _ leik): ub => [uE xb]; apply/(Ha _ leij); split; first Wtac.
    by rewrite (prl_prop3  leij lejk uE).
  move => t ta; apply:(qA _ _ lejk);apply/(Vf_image_P fjk hd).
  have hb: sub (Yo (gle (psr S) i k) (Vg A k \cap II k) (Vg A k)) (Vg A k).
     Ytac hx; fprops; apply: setI2_1.
  move /(Vf_image_P fjk (sub_trans hb hd) ): ta => [u ua ->]; exists u; fprops.
have cp1: gle prl_ne2_sigma_order A B.
  apply/graph_on_P1; split => // j jI; rewrite /B LgV//.
  Ytac hx; fprops; apply: setI2_1.
apply/singletonP; split; first ex_tac.
have lii:=  (prl_prop1 iI).
rewrite - (amax _ cp1) /B (LgV iI) (Y_true lii).
move => a b /setI2_P [ha /(Ha _ lii) [hb hc]] /setI2_P [qa /(Ha _ lii) [qb qc]].
by move:hc qc; rewrite (ps_identity_f iI) !idV // => ->.
Qed.


Lemma prl_ne2_sigma_maximal_prop3 A (xi := fun i =>  union (Vg A i)):
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  pr1_ne2_hyp3_weak ->
  maximal prl_ne2_sigma_order A ->
  (forall i, inc i (psI S) -> (Vg A i) = singleton (xi i))
  /\ inc  (Lg (psI S) xi) (projective_limit S).
Proof.
move => ha hb hc.
move:(prl_ne2_sigma_maximal_prop2 ha hb hc) => si.
have xip: forall i, inc i (psI S) -> (Vg A i) = singleton (xi i).
  by move => i iI; rewrite /xi; move:(si _ iI) => [t ->]; rewrite setU_1.
move:(prl_ne2_sigma_maximal_prop1 ha hc) => av.
have xiE i: inc i (psI S) ->  inc (xi i) (Vg (psE S) i).
  move => iI; apply/sub1setP;rewrite - (xip _ iI); apply/setP_P.
  move: (proj1 hc); rewrite (proj2 prl_ne2_sigma_osr) => /Zo_P [/setXb_P].
  rewrite FS_domain; move => [_ _ h] _.
  by move: ((FS_range iI) _ (h _ iI)).
have fij: forall i j, gle (psr S) i j -> xi i = Vf (Vg (psf S) (J i j)) (xi j).
  move => i j lij; move: (av _ _ lij).
  move: (prl_prop0 lij) => [iI jI].
  rewrite (xip _ iI) (xip _ jI) => ea.
  move:(prl_prop4 lij) => [ff sf tf].
  have hd:sub (singleton (xi j)) (source (Vg (psf S) (J i j))).
    by move => t /set1_P ->; rewrite sf; apply: xiE.
  by move:(set1_1 (xi i)); rewrite ea => /(Vf_image_P ff hd) [u /set1_P -> ub].
split => //; apply/prl_limitP; split.
- fprops.
- by aw.
- by move => i ii; rewrite LgV//; apply: xiE.
- move => i j lij; move: (prl_prop0 lij) => [iI jI].
  by rewrite ! LgV//; apply: fij.
Qed.

Lemma prl_ne2_sigma_maximal_ne A:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  pr1_ne2_hyp3_weak ->
  maximal prl_ne2_sigma_order A ->
  nonempty (projective_limit S).
Proof.
move => ha hb hc.
move: (proj2 (prl_ne2_sigma_maximal_prop3 ha hb hc)) => xx; ex_tac.
Qed.

  
Lemma prl_ne2_nonempty:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  pr1_ne2_hyp3_weak ->
  nonempty (projective_limit S).
Proof.
move => ha hb.
move:(Zorn_lemma (proj1 prl_ne2_sigma_osr)  (prl_ne2_sigma_inductive ha)).
move => [A Ap]; exact:(prl_ne2_sigma_maximal_ne ha hb Ap).
Qed.
  
Lemma prl_ne2_prop:
  (forall i, inc i (psI S) -> prl_ne1_condii' i) ->
  pr1_ne2_hyp3_plain ->
  prl_ne2_res_a.
Proof.                          
move => ha hb.
pose intv i:= (Zo (psI S) (gle (psr S) i)).
pose IIF i := intersectionf (intv i)(fun j=> Imf (Vg (psf S) (J i j))).
have Hw i:inc i (psI S) ->  nonempty (intv i).
  by move => iI; exists i; apply/Zo_P; split => //; apply: prl_prop1.
move => i iI; set_extens t.
  case:(prl_can_fun_fp iI) => [fc sc tc].
  move/(Imf_P fc); rewrite sc; move => [u ua ->].
  apply/(setIf_P _ (Hw _ iI)) => [j /Zo_P [ji lij]].
  case:(ps_function_f lij); aw =>  fij sij tij.
  apply/(Imf_P fij); rewrite sij (prl_proj_ev iI ua).
  move/(prl_limitP): ua => [qa qb qc qd].
  by exists (Vg u j); [apply: qc |apply: qd ].
move => tinter.
pose II j  := (Vfi1 (Vg (psf S) (J i j)) t).
have Ha k:  gle (psr S) i k ->
   ( forall x, inc x (II k) <-> 
               inc x (Vg (psE S) k) /\ t = Vf (Vg (psf S) (J i k)) x).
  move => lik x.
  move:(prl_prop4 lik) => [ff sf _]. rewrite - sf.
  by apply:iim_fun_set1_P.
pose Bi j := Yo (gle (psr S) i j) (II j) (Vg (psE S) j).
have tei: inc t (Vg (psE S) i).
  by move:(setIf_hi tinter (prl_ne2_int_i iI)); rewrite prl_ne2_im_of_id.
have qa: forall j, inc j (psI S) -> inc (Bi j) (Vg FS_fam j).
  rewrite /Bi;move => j jI; Ytac h; last by apply: FS_whole.
  apply: (hb _ _ _ h tei).
have qb: inc (Lg (psI S) Bi) (productb FS_fam).
  apply/setXb_P;split;aww;  rewrite FS_domain => //.
  by move => j jI; rewrite LgV//; apply: qa.
have qc j: inc j (psI S) -> nonempty (Vg (Lg (psI S) Bi) j).
  rewrite /Bi;move => jI; rewrite LgV//; Ytac lij; fprops.
  move/prl_ne2_intP: (lij) => jj; move:(setIf_hi tinter jj) => tt.
  move:(prl_prop4 lij) => [ff sf tf]. 
  move /(Imf_P ff): tt => [u usf tv].
  by exists u;  apply/(iim_fun_set1_P _ ff).
have sII k: gle (psr S) i k -> sub (II k) (Vg (psE S) k).
   by move => lik x /(Ha _ lik); case.
have Bsigma: inc (Lg (psI S) Bi) prl_ne2_sigma.
  apply/Zo_P; split => //; split => // j k ljk.
  move:(prl_prop0 ljk) => [jI kI].
  rewrite /Bi ! LgV// => u.
  move: (prl_prop4 ljk) => [fjk sjk tjk].
  case: (p_or_not_p (gle (psr S)  i j)) => lij; Ytac0.
    move: (proj33 (ps_preorder_r S) _ _ _ lij ljk) => lik; Ytac0.
    have hu: sub (II k) (source (Vg (psf S) (J j k))).
      by rewrite sjk; apply sII.
    move/(Vf_image_P fjk hu) => [v /(Ha _ lik) [ua ub] ->].
    apply/(Ha _ lij); split; first by Wtac.
    by rewrite (prl_prop3 lij ljk).
  have hu: sub (Yo (gle (psr S) i k) (II k) (Vg (psE S) k))
    (source (Vg (psf S) (J j k))).
    rewrite sjk;Ytac h; fprops.  
  move /(Vf_image_P fjk hu) => [v va ->]; Wtac.
move:prl_ne2_sigma_osr => [or osr].
rewrite - osr in Bsigma.
move: (inductive_max_greater or (prl_ne2_sigma_inductive ha) Bsigma).
move => [A Amax leBA].
move:(pr1_ne2_hyp3_weak_prop hb) => hb'.
move: (prl_ne2_sigma_maximal_prop3 ha hb' Amax)=> [ra rb].
move/graph_on_P1: leBA=> [_ _ h]; move:(h _ iI).
move:(prl_prop1 iI) => iir.
rewrite (ra _ iI); set xx := union _ => /sub1setP.
rewrite /Bi LgV//; Ytac0; move/(Ha _ iir) => [xe ->].
rewrite (ps_identity_f iI) (idV xe).
move:(prl_can_fun_fp iI) => [ff sf tf].
apply/(Imf_P ff); rewrite sf; ex_tac.
rewrite prl_proj_ev // LgV//.
Qed.


End ProjectiveLimitNonEmpty2.

    
(** Inductive systems *)

Record inductive_system: Type := InductiveSystem {
  isE : Set;
  isI : Set;
  isr : Set;
  isf : Set;
  is_preorder_r: preorder isr;
  is_substrate_r: substrate isr = isI;
  is_directed_r: right_directed_on isr isI;
  is_fgraph_E: fgraph isE;
  is_domain_E: domain isE = isI;
  is_fgraph_f: fgraph isf;
  is_domain_f: domain isf = isr;
  is_function_f:
    forall p, inc p isr ->
              function_prop (Vg isf p) (Vg isE (P p)) (Vg isE (Q p));
  is_compose_f: forall i  j k, gle isr i j -> gle isr j k ->
                  Vg isf (J j k) \co  Vg isf (J i j) = Vg isf (J i k);
  is_identity_f: forall i, inc i isI -> Vg isf (J i i) = identity (Vg isE i)
}.


Definition inductive_system_on S E I r f :=
  [/\ isE S =  E, isI S = I, isr S = r & isf S = f].


Definition inl_same_data S S' := 
 [/\ isE S = isE S', isr S = isr S' & isf S = isf S'].

Lemma inl_same_dataS S S':
  inl_same_data S S' -> inl_same_data S' S.
Proof. by move => [pa pb pc]. Qed.

Lemma inl_same_dataT S S' S'' :
  inl_same_data S S' ->  inl_same_data S' S'' -> inl_same_data S S''.
Proof.
by rewrite /inl_same_data; move => [-> -> ->]. 
Qed.


Definition inl_same_index S S' := isr S = isr S'.

Lemma inl_same_index_same_I S S': 
  inl_same_index S S' -> isI S = isI S'.
Proof. by rewrite - !is_substrate_r => ->. Qed.

Lemma inl_prop0 S i j: gle (isr S) i j -> inc i (isI S) /\ inc j (isI S).
Proof.
move=> h; rewrite - is_substrate_r; split; order_tac.
Qed.

Lemma inl_prop1 S i: inc i (isI S) -> inc (J i i) (isr S).
Proof.
move => iI.
by apply:(proj32 (is_preorder_r S)); rewrite is_substrate_r.
Qed.

Lemma inl_prop2 S i j k: gle (isr S) i j -> gle (isr S) j k ->
  Vg (isf S) (J j k) \coP  Vg (isf S) (J i j).
Proof.
rewrite /composable.
by move => /is_function_f [fa  sa ->] /is_function_f [fb -> tb]; aw.
Qed.

Lemma inl_prop3 S y i j k (f:= isf S):
  gle (isr S) i j -> gle (isr S) j k -> inc y (Vg (isE S) i) ->
  Vf (Vg f (J j k))  (Vf (Vg f (J i j)) y) = Vf (Vg f (J i k)) y.
Proof.
move => lij ljk yv.
have co:= (inl_prop2 lij ljk).
move:(f_equal (Vf^~ y) (is_compose_f lij ljk)); rewrite compfV // => //.
by move:(is_function_f lij) => [_ -> _];aw.
Qed.

Lemma inl_prop4 S i j: gle (isr S) i j -> 
  function_prop (Vg (isf S) (J i j)) (Vg (isE S) i) (Vg (isE S) j).
Proof.
by move/(is_function_f); aw.
Qed.

Lemma inl_prop5 S i x: inc i (isI S) -> inc x (Vg (isE S) i) ->
   Vf (Vg (isf S) (J i i)) x = x.
Proof.
move => iI xE; rewrite (is_identity_f iI) idV //.
Qed.

Definition inl_sum S := disjointU (isE S).

Definition inl_equiv_rel S x y:=
  exists k, [/\ gle (isr S) (Q x) k,  gle (isr S) (Q y) k   &
   Vf (Vg (isf S) (J (Q x) k)) (P x) =  Vf (Vg (isf S) (J (Q y) k)) (P y) ].

Definition inl_equiv S := graph_on(inl_equiv_rel S)  (inl_sum S) .

Lemma inl_sumP S x: inc x (inl_sum S) <->
  [/\ pairp x, inc (Q x) (isI S) & inc (P x) (Vg (isE S) (Q x))].
Proof.
split; first by case/disjointU_P; rewrite is_domain_E. 
by move => [ha hb hc]; apply /disjointU_P; rewrite is_domain_E. 
Qed.

Lemma inl_equiv_reflexive S a: inc a (inl_sum S) -> inl_equiv_rel S a a.
Proof.
by move/inl_sumP => [ _ /inl_prop1 pb _];exists (Q a).  
Qed.

Lemma inl_equiv_esr S: equivalence_on (inl_equiv S) (inl_sum S).
Proof.
split; last by apply: graph_on_sr; apply:inl_equiv_reflexive.
have ->: (inl_equiv S) = graph_on (fun a b =>
   [/\ inc a (inl_sum S), inc b (inl_sum S) & inl_equiv_rel S a b]) (inl_sum S).
  by apply: Zo_exten1 => t /setX_P [_ px qx]; split => // [] [_ _].
apply: equivalence_from_rel; split.
  by move => x y [xs ys [k [ha hb hc]]]; split => //;exists k; split.
move=> y x z [xE yE [k [lxik lyik vfxik_yik]]] [_ zE [l [lyil lzil vfyil_zil]]].
split => //.
move: (arg2_sr lxik)(arg2_sr lyil); rewrite is_substrate_r => kI lI.
move:(is_directed_r kI lI) => [i [ iI lki lli]].
exists i; split => //.
- exact:(proj33 (is_preorder_r S) _ _ _ lxik lki).
- exact:(proj33 (is_preorder_r S) _ _ _ lzil lli).
move/inl_sumP: xE => [_ aI xE].
move/inl_sumP: yE => [_ bI yE].
move/inl_sumP: zE => [_ cI zE].
move: (inl_prop3  lxik  lki xE) (inl_prop3  lyik  lki yE).
rewrite vfxik_yik ; move => -> ->.
move: (inl_prop3  lyil  lli yE) (inl_prop3  lzil lli zE).
by rewrite vfyil_zil; move => ->.
Qed.

Lemma inl_equiv_sr S: substrate (inl_equiv S) =  (inl_sum S).
Proof. exact (proj2 (inl_equiv_esr S)).  Qed.


Lemma inl_class_eq S x y:
  inc x (inl_sum S) -> inc y (inl_sum S)  ->
  (class (inl_equiv S) x = class (inl_equiv S) y
     <-> inl_equiv_rel S x y).
Proof.
have [ha hb] := inl_equiv_esr S.
move => xE yE; move: (xE)(yE); rewrite - hb => xsr ysr.
split => xx.
  by move/(related_equiv_P ha): (And3 xsr ysr xx) => /graph_on_P1 [].
by apply/(class_eq1 ha); apply/graph_on_P1.
Qed.  

Lemma inl_class_eq_bis S i j x y:
  inc i (isI S) -> inc j (isI S) ->
  inc x (Vg (isE S) i) ->  inc y (Vg (isE S) j) ->
  (class (inl_equiv S) (J x i) = class (inl_equiv S) (J y j)
   <-> inl_equiv_rel S (J x i) (J y j)).
Proof.
move => ha hb hc hd.
by apply: inl_class_eq; apply/inl_sumP; aw; split; fprops.
Qed.

Lemma inl_class_of_fij S i j x:
  gle (isr S) i j -> inc x (Vg (isE S) i) ->
  class (inl_equiv S) (J (Vf (Vg (isf S) (J i j)) x) j) =
  class (inl_equiv S) (J x i). 
Proof.
move => lij xE.
move: (inl_prop0 lij) => [iI jI].
move: (inl_prop4 lij) => [fij sij tij].
have fiE:inc (Vf (Vg (isf S) (J i j)) x) (Vg (isE S) j) by Wtac.
symmetry;apply/(inl_class_eq_bis iI jI xE fiE).
exists j; aw; split => //; first  exact:inl_prop1.
rewrite (inl_prop5 jI) //; Wtac.
Qed.


Lemma inl_equivalence_prop S R:
  equivalence R -> 
  (forall i j x,
    gle (isr S) i j -> inc x (Vg (isE S) i) ->
    related R (J x i) (J (Vf (Vg (isf S) (J i j)) x) j)) ->
  forall a b, related (inl_equiv S)  a b -> related R a b.
Proof.
move => [_ _ p3 p4] hc a b /graph_on_P1 [ad bd [k [lik ljk]] sv].
move/(inl_sumP): ad => [a1 a2 a3].
move/(inl_sumP): bd => [b1 b2 b3].
move: (hc (Q a) k (P a) lik a3).
move: (hc (Q b) k (P b) ljk b3).
rewrite sv a1 b1 => r1 r2; exact: (p3 _ _ _ r2 (p4 _ _ r1)).
Qed.


Definition inductive_limit S := quotient (inl_equiv S).

Lemma inductive_limitP S x:
  inc x (inductive_limit S) <-> classp  (inl_equiv S) x.
Proof.
exact:(setQ_P (proj1 (inl_equiv_esr S)) x).
Qed.

Lemma inl_class_in_lim S i x:
   inc i (isI S) -> inc x (Vg (isE S) i) ->
   inc (class (inl_equiv S) (J x i)) (inductive_limit S).
Proof.
move => iI xE; apply/inductive_limitP.
have [ha hb]:=(inl_equiv_esr S).
apply:(class_class ha); rewrite hb; apply/inl_sumP; aw; split; fprops.
Qed.

Lemma inductive_limit_hi S x (i := (Q (rep x))) (y := P (rep x)):
  inc x (inductive_limit S) -> 
  [/\ inc i (isI S), inc y (Vg (isE S) i) & x = class (inl_equiv S) (J y i)].
Proof.
case/inductive_limitP; rewrite inl_equiv_sr.
by move  => /inl_sumP [pp px qx ->]; rewrite pp.
Qed.

Lemma inl_limit_nonempty S:
  (exists2 i, inc i (isI S) & nonempty (Vg (isE S) i)) <->
  nonempty (inductive_limit S). 
Proof.
split.
  move => [i iI [x xe]]; move: (inl_class_in_lim iI xe) => cs; ex_tac.
move => [x /inductive_limit_hi [ha hb _]]; ex_tac; ex_tac.
Qed.

Definition inl_can_fun S i :=
  Lf (fun x => class (inl_equiv S) (J x i)) (Vg (isE S) i) (inductive_limit S).

Lemma  inl_can_fun_ax S i :
  inc i (isI S) ->
  lf_axiom (fun x => class (inl_equiv S) (J x i)) (Vg (isE S) i)
           (inductive_limit S).
Proof.
move => iI x xE; apply: inc_class_setQ.
rewrite inl_equiv_sr; apply/inl_sumP;aw; split ; fprops.
Qed.

Lemma inl_can_fun_fp S i: inc i (isI S) ->
  function_prop (inl_can_fun S i)  (Vg (isE S) i) (inductive_limit S).
Proof.
move => ide; rewrite /inl_can_fun.
saw; apply:lf_function; exact:inl_can_fun_ax.
Qed.

Lemma inl_can_fun_ev S i x:  inc i (isI S) -> inc x (Vg (isE S) i) ->
  Vf (inl_can_fun S i) x = class (inl_equiv S) (J x i).
Proof.
by move => iI xE; rewrite /inl_can_fun LfV//; apply:inl_can_fun_ax.
Qed.
  
Lemma inl_can_fun_prop S i j (f := isf S)
      (fi := inl_can_fun S i) (fj := inl_can_fun S j):
   gle (isr S) i j ->
   (fj \coP Vg f (J i j) /\  fi = fj \co (Vg f (J i j))).
Proof.
move => lij.
move:(inl_prop4 lij) => [fij sij tij].
move:(inl_prop0 lij)=> [iE jE].
move:(inl_can_fun_fp iE) => [ffi si ti].
move:(inl_can_fun_fp jE) => [ffj sj tj].
have pd: source fj = target (Vg f (J i j)) by ue.
have pe: fj \coP Vg f (J i j) by split.
have pf:=(compf_f pe).
have pg: target fi = target fj by rewrite ti tj.
have ph: source fi = source (Vg f (J i j)) by ue.
split => //; apply:function_exten => //; aw; trivial.
  move => x xsf /=; rewrite compfV//; last ue.
rewrite ph sij in xsf.
have vix: inc (Vf (Vg (isf S) (J i j)) x) (Vg (isE S) j) by Wtac.
by rewrite /fi /fj !inl_can_fun_ev // (inl_class_of_fij lij).
Qed.


Lemma inl_equiv_Iv S S':
  inl_same_data S S' -> inl_equiv S = inl_equiv S'.
Proof.
move => [sa sb sc].
by rewrite /inl_equiv/inl_sum /inl_equiv_rel sa sb sc. 
Qed.


Lemma inductive_limit_Iv S S':
  inl_same_data S S' -> inductive_limit S = inductive_limit S'.
Proof.
by move / inl_equiv_Iv;rewrite  /inductive_limit => ->.
Qed.

Lemma inl_can_fun_Iv S S' i:
  inl_same_data S S' ->
  inl_can_fun S i = inl_can_fun S' i.
Proof.
move=> H; rewrite /inl_can_fun (inductive_limit_Iv H) (inl_equiv_Iv H).
by rewrite (proj31 H).
Qed.

Section InjExample1.  
Variable A B I V r: Set.

Hypotheses (or: preorder r)(sr: substrate r = I) (rdr: right_directed_on r I).
Hypothesis Vprop:
  [/\ fgraph V, domain V = I, (forall i, inc i I -> sub (Vg V i) A) &
    forall i j, gle r i j -> sub (Vg V j) (Vg V i)].

Definition Injex1_E := Lg I (fun i => functions (Vg V i) B).

Definition Injex1_ff p :=
  Lf (fun f => restriction f (Vg V (Q p)))
    (Vg Injex1_E (P p)) (Vg Injex1_E (Q p)).


Lemma Injex1_ff_ax p : inc p r ->
  lf_axiom (fun f => restriction f (Vg V (Q p)))
    (Vg Injex1_E (P p)) (Vg Injex1_E (Q p)).
Proof.
move => pr f.
move: (pr1_sr pr)(pr2_sr pr); rewrite sr => pI qI.
move:(proj31 or _ pr) => pp; move:(pr); rewrite -{1}pp => gle1.
rewrite /Injex1_E ! LgV//; move/functionsP => [ff sf tf].
move:(proj44 Vprop _ _ gle1); rewrite -{1} sf => sub1.
apply/functionsP;  rewrite - tf;exact:(restriction_prop ff  sub1).
Qed.

Lemma Injex1_ff_p p: inc p r -> 
   function_prop (Injex1_ff p) (Vg  Injex1_E (P p)) (Vg  Injex1_E (Q p)).
Proof.
move => pr; rewrite /Injex1_ff; saw.
by apply: lf_function; apply: Injex1_ff_ax.
Qed.

Definition  Injex1_system: inductive_system.
apply(@InductiveSystem Injex1_E I r (Lg r Injex1_ff)).
- exact.
- exact.
- exact.
- rewrite/Injex1_E; fprops.
- by rewrite/Injex1_E; aw.
- fprops.
- by aw.
- by move => p pr; rewrite LgV//;apply:Injex1_ff_p.
- move => i j k leij lejk; move:(proj33 or _ _ _ leij lejk) => leik.
  rewrite ! LgV//.
  case:(Injex1_ff_p leij);aw => fij sij tij.
  case:(Injex1_ff_p lejk);aw => fjk sjk tjk.
  case:(Injex1_ff_p leik);aw => fik sik tik.
  have xx: Injex1_ff (J j k) \coP Injex1_ff (J i j) by split => //; ue.
  apply: function_exten; [  by apply:compf_f | done | aw; ue | aw; ue | ].
  move:(Injex1_ff_ax leij)(Injex1_ff_ax leik)(Injex1_ff_ax lejk).
  aw; rewrite sij; move => a1 a2 a3 gf fs; rewrite compfV //; last by ue.
  rewrite /Injex1_ff; aw; rewrite LfV // LfV// ? LfV//.
    rewrite /restriction;aw; rewrite double_restr //.
    by apply: (proj44 Vprop).
   by move: (a1 gf fs);aw.
- move => i iI.
  have  iir: inc (J i i) r by apply:(proj32 or i); rewrite sr.
  move:(Injex1_ff_p iir); rewrite LgV //; aw => ff; apply:(identity_prop0 ff) => f fe.
  move:(Injex1_ff_ax  iir); aw => ax.
  rewrite /= /Injex1_ff; aw; rewrite LfV//.
  move: fe; rewrite / Injex1_E ! LgV // => /functionsP [fa sa ta].
  by rewrite restriction_Lf // - sa //  (lf_recovers fa).
Defined.

Lemma  Injex1_system_val:
  inductive_system_on Injex1_system Injex1_E I r (Lg r Injex1_ff).
Proof. done. Qed.
End InjExample1.  


Section InjExample2.  
Variable  F I r: Set.

Hypotheses (or: preorder r)(sr: substrate r = I) (rdr: right_directed_on r I).

Definition  Injex2_system: inductive_system.
apply(@InductiveSystem  (cst_graph I F) I r (cst_graph r (identity F))).
- exact.
- exact.
- exact.
- fprops.
- by aw.
- fprops.
- by aw.
- move => p pr; move:(pr1_sr pr)(pr2_sr pr); rewrite sr => pI qI.
  rewrite ! LgV//; apply: identity_prop.
- move => i j k lij ljk;  move:(proj33 or _ _ _ lij ljk) => leik.
  rewrite ! LgV//; apply: compf_id_id.
- by move => i iI;rewrite ! LgV//;apply:(proj32 or i); rewrite sr.
Defined.

Lemma Inj_ex2_val: inductive_system_on Injex2_system
    (cst_graph I F) I r (cst_graph r (identity F)).
Proof. by []. Qed.


Lemma Inj_ex2_can_prop x y (E := (inl_sum Injex2_system)):
  related (inl_equiv Injex2_system) x y <->
  [/\ inc x E, inc y E & P x = P y].
Proof.
move: (Inj_ex2_val) => [eqE eqI eqr eqf].
split.
  move/graph_on_P1 =>[xE yE [k [ka kb kc]]]; split => //.
  move/inl_sumP:xE;move/inl_sumP:yE;rewrite eqI eqE.
  move => [_ qy py][_ qx px]; move: py px; rewrite !LgV// => py px.
  move: kc; rewrite eqf ! LgV //! idV//.
move => [xE yE sp]; apply/graph_on_P1; split => //.
move/inl_sumP:xE;move/inl_sumP:yE;rewrite eqI eqE.
move => [_ qy py][_ qx px]; move: py px; rewrite !LgV// => py px.
move:(rdr qx qy) => [k  [kI ka kb]].
exists k; rewrite eqr eqf ! LgV // !idV //.
Qed.
 

Lemma Inj_ex2_can_fun (E := (inductive_limit Injex2_system)):
  nonempty I ->
  bijection_prop (Lf (fun z => (P (rep z))) E F) E F.
Proof.
move: (Inj_ex2_val) => [eqE eqI eqr eqf] neI.
have [eqv esr]:=(inl_equiv_esr Injex2_system).
saw; apply: lf_bijective.
+ move => t /inductive_limitP []; rewrite esr => /inl_sumP [_ ha hb] _.
   move: hb;rewrite eqE LgV //.
+ move => u v /inductive_limitP [ha {2} ->]  /inductive_limitP [hb {2} ->] sp.
  rewrite esr in ha hb.
  by apply: (class_eq1 eqv); apply/Inj_ex2_can_prop.
+ move: neI => [i iI] y yF.
  have hu: inc (J y i) (substrate (inl_equiv Injex2_system)).
    rewrite esr;apply/inl_sumP; aw;rewrite eqE eqI LgV//; split; fprops.
  exists (class ((inl_equiv Injex2_system)) (J y i)).
    by apply:inc_class_setQ.
  by move:(related_rep_class eqv hu); move/Inj_ex2_can_prop => [_ _]; aw.
Qed.

End InjExample2. 

Lemma finite_preorder_directed_bounded r I E:
  preorder r -> substrate r = I -> right_directed_on r I->
  nonempty E -> finite_set E -> sub E I -> 
  exists2 x, inc x I & forall y, inc y E -> gle r y x.
Proof.
move=> or sr rdr ha hb hc.
suff: exists x, forall y : Set, inc y E -> gle r y x.
  move => [x xp]; exists x => //; move:ha => [y yE].
  move:(arg2_sr (xp _ yE)); ue.
move: E hb ha hc; apply:(finite_set_induction3). 
- move => a b aI bI; move:(rdr _ _ aI bI) => [c [cI ca cb]]; exists c.
  by  move => t /set2_P [] ->.
- move => a b x y aI bI pa pxb t /setU1_P.
  move:(pxb _ (set2_1 x b)) (pxb _ (set2_2 x b)) => xy lyb.
  case; [ by move/pa => tx; apply: (proj33 or _ _ _ tx xy) | by move ->].
- by move => X x XI [a aX] h; move: (arg2_sr (h _ aX)); ue.
Qed.
            
Lemma inl_Lemma5_1i S X (K:= domain X)
  (Y := fun a => Lg K (fun i => Vf (Vg (isf S) (J (Q (rep (Vg X i))) a))
                            (P (rep (Vg X i))))):
  fgraph X -> finite_set K -> nonempty K ->
  (forall i, inc i K -> inc (Vg X i)  (inductive_limit S)) ->
  exists2 a, inc a (isI S) &
      [/\ fgraph (Y a), domain (Y a) = K &
     forall i, inc i K -> Vg X i =  Vf (inl_can_fun S a) (Vg (Y a) i) ].
Proof.
move => fgX fsK neK XE.  
have ha: forall i, inc i K -> inc (Q (rep (Vg X i))) (isI S).
  by move => i /XE /inductive_limitP []; rewrite inl_equiv_sr; case/inl_sumP.
set IK := fun_image K (fun i => (Q (rep (Vg X i)))).
have neik: nonempty IK by apply:funI_setne.
have fsk: finite_set IK by apply: finite_fun_image.
have sik: sub IK (isI S) by  move => t/ funI_P [z zK ->]; apply: ha.
move: (finite_preorder_directed_bounded  (is_preorder_r S) (is_substrate_r S)
   (@is_directed_r S) neik fsk sik) => [a aI ap].
ex_tac.
have ap2 i: inc i K -> gle (isr S) (Q (rep (Vg X i))) a.
   move => iK; apply:ap; apply/funI_P; ex_tac.
rewrite /Y;split; aww =>  i iK; rewrite LgV//.
move: (XE _ iK) => /inductive_limit_hi [pa pb {1} ->].
set y := (Vf (Vg _ _) _).
have yiE: inc y (Vg (isE S) a). 
  move:(inl_prop4 (ap2 _ iK)) => [ff sf tf]; rewrite /y; Wtac.
rewrite (inl_can_fun_ev aI yiE);apply/(inl_class_eq_bis) =>  //.
exists a; aw;split; fprops.
   by apply: inl_prop1.
by aw; rewrite inl_prop5.
Qed.

Definition constant_fun_on f X := forall i j,
  inc i X -> inc j X -> Vf f i = Vf f j.
      
Lemma inl_Lemma5_1ii S i X:
  inc i (isI S) -> sub X (Vg (isE S) i) -> finite_set X ->
  constant_fun_on (inl_can_fun S i) X ->
  exists2 j, gle (isr S) i j & constant_fun_on (Vg (isf S) (J i j)) X. 
Proof.
move => iI ha hb hc.
case: (emptyset_dichot X).
  by move => ->; exists i; [apply: (inl_prop1 iI) | move => x y /in_set0].
move => neX.
have [eqv seqv]:=(inl_equiv_esr S).
have ra: forall x y, inc x X -> inc y X ->
   exists2 k, gle (isr S) i k &
            Vf (Vg (isf S) (J i k)) x = Vf (Vg (isf S) (J i k)) y.
  move => x y xX yX; move: (hc _ _ xX yX).
  rewrite (inl_can_fun_ev iI (ha _ xX)) (inl_can_fun_ev iI (ha _ yX)).
  move/(inl_class_eq_bis iI iI (ha _ xX) (ha _ yX)) => [k []].
  by aw => lik svk; exists k.
pose M p := fun k =>  gle (isr S) i k /\
         Vf (Vg (isf S) (J i k)) (P p) = Vf (Vg (isf S) (J i k)) (Q p).
pose C p :=  choose (M p).
have rb: forall p, inc p (coarse X) ->  M p (C p).
   move => p /setX_P [pp p1 p2]; apply:choose_pr.
   by move:(ra _ _ p1 p2) => [k ka kb]; exists k.
have rc:  forall p, inc p (coarse X) ->  inc (C p) (isI S).
  by move => p/rb [/arg2_sr]; rewrite is_substrate_r.
set IK := fun_image (coarse X) C. 
set x1 := (J (rep X) (rep X)).
have x1C : inc x1 (coarse X) by  apply:setXp_i; apply: rep_i.
have cx1_IK: inc (C x1) IK by apply:funI_i.
have neik: nonempty IK by ex_tac.
have fsk: finite_set IK by apply: finite_fun_image; apply: finite_prod2.
have sik: sub IK (isI S) by  move => t/ funI_P [z zK ->]; apply: rc.
move: (finite_preorder_directed_bounded  (is_preorder_r S) (is_substrate_r S)
   (@is_directed_r S) neik fsk sik) => [a aI ap].
move: (proj33 (is_preorder_r S) _ _ _ (proj1 (rb _ x1C)) (ap _ cx1_IK)) => lia.
exists a => // x y xX yX.
move: (setXp_i xX yX) => pc.
have C_IK: inc (C (J x y)) IK by apply:funI_i.
case:(rb _ pc); aw => ca cb.
have cc := (ap  _ C_IK).
by rewrite -(inl_prop3 ca cc (ha _ xX)) -(inl_prop3 ca cc (ha _ yX)) cb.
Qed.

(** Direct systems of mappings *)

Definition inl_map_compat S u F:=
  [/\ fgraph u, domain u = isI S, 
   forall i, inc i (isI S) -> function_prop (Vg u i) (Vg (isE S) i) F &
   forall i j, gle (isr S) i j -> (Vg u j) \co Vg (isf S) (J i j) = Vg u i].

Definition inl_map_property S u F g:=
  function_prop g (inductive_limit S) F /\
  forall i, inc i (isI S) -> (Vg u i) = g \co (inl_can_fun S i).


Lemma inl_map_compat0 S u F i j x:
  inl_map_compat S u F -> gle (isr S) i j -> inc x (Vg (isE S) i) ->
  (Vf (Vg u i)) x = Vf (Vg u j) (Vf (Vg (isf S) (J i j)) x).
Proof.
move => [a hb hc hd] lij xi.
move:(inl_prop0 lij) => [iI jI].
move: (inl_prop4 lij) => [fij sij tij].
move:(hc _ jI) => [fu su tu].
have co: Vg u j \coP Vg (isf S) (J i j) by split => //; ue.
have xs:  inc x (source (Vg (isf S) (J i j))) by ue.
rewrite -(hd _ _ lij); rewrite compfV//.
Qed.


Lemma inl_map_property_res1 S u F g i x:
  inl_map_compat S u F -> inl_map_property S u F g ->
  inc i (isI S) -> inc x (Vg (isE S) i) ->
  Vf g (class (inl_equiv S) (J x i)) = Vf (Vg u i) x.
Proof.
move => [p1 p2 p3 p4] [[fg sg tg] hb] hc hd.
move:(inl_can_fun_fp hc) => [fc sc tc].
have co: g \coP inl_can_fun S i by split => //; ue.
have xs: inc x (source (inl_can_fun S i)) by ue.
rewrite (hb _ hc); rewrite compfV//.
by rewrite /inl_can_fun LfV//; apply: inl_can_fun_ax.
Qed.


Lemma inl_map_unique S u F g g':
  inl_map_compat S u F ->
  inl_map_property S u F g -> inl_map_property S u F g' -> g = g'.
Proof.
move => ha hb hc.
have seqv:=(inl_equiv_sr S).
move:(proj1 hb) (proj1 hc) => [fg sg tg] [fg' sg' tg'].
apply: function_exten => //; try ue.
rewrite sg => x /inductive_limitP [rs ->].
move: rs; rewrite seqv => /inl_sumP [pr p1 p2]. 
rewrite - pr.
rewrite (inl_map_property_res1 ha hb p1 p2).
by rewrite (inl_map_property_res1 ha hc p1 p2).
Qed.

Definition inl_map_val u := fun y => Vf (Vg u (Q (rep y))) (P (rep y)).
Definition inductive_map S u F:=
  Lf (inl_map_val u) (inductive_limit  S) F.
  
Lemma inl_map_ax S u F:
  inl_map_compat S u F ->
  lf_axiom (inl_map_val u) (inductive_limit  S) F.
Proof.
move => [p1 p2 p3 p4] x /inductive_limit_hi [ha hb hc].
move:(p3 _ ha) => [fg sg tg]; rewrite /inl_map_val; Wtac.
Qed.

Lemma inl_map_prop  S u F:
  inl_map_compat S u F ->
  inl_map_property  S u F (inductive_map S u F).
Proof.
move => h.
move:(inl_map_ax h) => ax.
have ra:function_prop (inductive_map S u F) (inductive_limit S) F.
  by rewrite /inductive_map; saw; apply: lf_function.
move: h => [p1 p2 p3 p4].
split => // i iI.
move: ra (p3 _ iI) => [fa sa ta] [fb sb tb].
move:(inl_can_fun_fp iI) => [fc sc tc].
have cc: (inductive_map S u F \coP inl_can_fun S i) by split; fprops; ue.
apply: function_exten => //; aw; try ue; first by apply:compf_f.
rewrite sb => x xEi; rewrite compfV//; last by ue.
have xiE: inc (J x i) (inl_sum S) by apply/inl_sumP;split; aww.
have ha:inc (Vf (inl_can_fun S i) x) (inductive_limit S) by Wtac.
rewrite /inductive_map/inl_map_val LfV//.
move: ha; rewrite (inl_can_fun_ev iI xEi).
move/inductive_limitP => []; rewrite inl_equiv_sr => yE.
move/(inl_class_eq xiE yE) => [k[]]; aw; set y := rep _ => lik ljk sv.
rewrite - (f_equal (Vf ^~ x) (p4 _ _ lik)).
rewrite - (f_equal (Vf ^~ (P y)) (p4 _ _ ljk)).
move:(inl_prop4 lik) => [fik sik tik].
move:(inl_prop4 ljk) => [fjk sjk tjk].
move: (arg2_sr lik); rewrite is_substrate_r => /p3 [fu su tu].
have co1: Vg u k \coP Vg (isf S) (J (Q y) k) by split => //; ue.
have co2: Vg u k \coP Vg (isf S) (J i k) by split => //; ue.
by rewrite ! compfV//; try ue; rewrite sjk;move /inl_sumP: yE => [_ _]. 
Qed.


Lemma inl_inductive_map_ev  S u F i x:
  inl_map_compat S u F -> inc i (isI S) -> inc x (Vg (isE S) i) ->
  Vf (inductive_map S u F) (class (inl_equiv S) (J x i)) = Vf (Vg u i) x.
Proof.
move => ha.
move:(inl_map_prop ha) => hb.
move => iI xE; exact: (inl_map_property_res1 ha hb iI xE). 
Qed.

Lemma inl_map_surjective  S u F:
  inl_map_compat S u F ->
  (surjection (inductive_map S u F) <->
    F = unionf (isI S) (fun i => Imf (Vg u i))).
Proof.
move => h0; move:(inl_map_prop h0) => h1.
move: (h1) => [[fu su tu]  cu].
split => h2.
  move: (h0) => [fgu du uv1 uv2].
  set_extens t.
    rewrite - tu => tt; move: (proj2 h2 _ tt); rewrite su;move => [x xs ->].
    move/inductive_limit_hi: xs => [pa pb ->]; apply/setUf_P; ex_tac.
    rewrite (inl_map_property_res1 h0 h1 pa pb). 
    move:(uv1 _ pa) => [fui sui tui].
    apply/(Imf_P fui); rewrite sui; ex_tac. 
  move/setUf_P => [i iI].
  move:(uv1 _ iI) => [fui sui tui].
  case/(Imf_P fui); rewrite sui => [x xE ->]; Wtac.
split => //; rewrite tu su {1} h2 => y yF. 
move/setUf_P: yF => [i iI].
move: (h0) => [fgu du uv1 uv2].
move:(uv1 _ iI) => [fui sui tui]; move/(Imf_P fui); rewrite sui.
move => [x xE ->].
exists (class (inl_equiv S) (J x i)); first by apply:inl_class_in_lim.
symmetry; exact:(inl_map_property_res1 h0 h1 iI xE). 
Qed.

Lemma inl_map_injective  S u F:
  inl_map_compat S u F ->
  (injection (inductive_map S u F) <->
   forall i x y, inc i (isI S) ->
                 inc x (Vg (isE S) i) -> inc y (Vg (isE S) i) ->
                 Vf (Vg u i) x = Vf (Vg u i) y ->
    exists2 j, gle (isr S) i j &
        Vf (Vg (isf S) (J i j)) x =  Vf (Vg (isf S) (J i j)) y). 
Proof.
move => h0.
move:(inl_map_prop h0) => h1.
move: (h1) => [[fu su tu]  cu].
have [eqv seqv]:=(inl_equiv_esr S).
split.
  move=> [_ inj] i x y iI xE yE sv.
  rewrite su in inj.
  move: (inl_class_in_lim iI xE) (inl_class_in_lim iI yE) => c1 c2.
  move: sv; rewrite -(inl_inductive_map_ev h0 iI xE).
  rewrite -(inl_inductive_map_ev h0 iI yE) => ee.
  move: (inj _ _ c1 c2 ee).
  by move => /(inl_class_eq_bis iI iI xE yE) [k []]; aw => ha _ hb; exists k.
move => h.
split => //; rewrite su => x y /inductive_limit_hi [rxi rxE ->].
move /inductive_limit_hi => [ryi ryE ->].
rewrite (inl_map_property_res1 h0 h1 rxi rxE).
rewrite (inl_map_property_res1 h0 h1 ryi ryE).
move:(is_directed_r  rxi ryi) => [k [kI lik ljk]].
rewrite (inl_map_compat0 h0 lik rxE) (inl_map_compat0 h0 ljk ryE).
set xa := (Vf (Vg (isf S) (J (Q (rep x)) k)) _).
set ya := (Vf (Vg (isf S) (J (Q (rep y)) k)) _) => eqa.
move: (inl_prop4 lik) => [fik sik tik].
move: (inl_prop4 ljk) => [fjk sjk tjk].
have xas: inc xa (Vg (isE S) k) by rewrite /xa; Wtac.
have yas: inc ya (Vg (isE S) k) by rewrite /ya; Wtac.
rewrite -(inl_class_of_fij lik rxE) - (inl_class_of_fij ljk ryE).
apply/(inl_class_eq_bis kI kI xas yas).
move:(h _ _ _ kI xas yas eqa) => [j lkj jp].
exists j; saw.
Qed.

Lemma inl_can_fun_inj S:
  (forall p, inc p (isr S) -> injection (Vg (isf S) p)) ->
  (forall i, inc i (isI S) -> injection (inl_can_fun S i)).
Proof.
move => h i iI.
move:(inl_can_fun_fp iI) => [ff sf tf].
split => //; rewrite sf => x y xs ys.
rewrite (inl_can_fun_ev iI xs) (inl_can_fun_ev iI ys).
move/(inl_class_eq_bis iI iI xs ys) => [k []];aw; move => lij _ etc.
move: (proj2 (h _ lij)); rewrite (proj32 (inl_prop4 lij)) => h'.
exact:(h' _ _ xs ys etc).
Qed.

(* Noter et deplacer *)

Lemma ci_fp A B: sub A B -> function_prop (canonical_injection A B) A B.
Proof.
move => sAB; split; first by apply:ci_f.
rewrite /canonical_injection; aw; trivial.
by rewrite /canonical_injection; aw.
Qed.

Lemma ci_compose A B C (fAB := canonical_injection A B)
      (fBC := canonical_injection B C)(fAC := canonical_injection A C):
  sub A B -> sub B C -> fBC \co fAB = fAC.
Proof.
move => hAB hBC; move: (sub_trans hAB hBC) => hAC.
move:(ci_fp hAB)(ci_fp hBC)(ci_fp hAC)=>[fij sij tij][fjk sjk tjk][fik sik tik].
have co: fBC \coP fAB by split => //; ue.
apply: function_exten;aw; trivial;try ue; first by apply: compf_f.
move => x xs /=; rewrite compfV //.
have xA: inc x A by ue.
have xB: inc x B by apply: hAB.
by rewrite /fAB /fBC /fAB /canonical_injection !ci_V.
Qed.

Lemma ci_image A B: sub A B -> 
   Imf (canonical_injection A B) = A.
Proof.
move => h; move:(ci_fp h) => [ff sf tf].
set_extens t.
  by move/(Imf_P ff); rewrite sf;move => [u uA ->]; rewrite ci_V.
by move => tA; apply/(Imf_P ff); rewrite sf; ex_tac;rewrite ci_V.
Qed.
 
Section InlRemark.

Variables (I r F:Set).
  
Hypotheses (or: preorder r)(sr: substrate r = I) (rdr: right_directed_on r I).
Hypotheses (fgF: fgraph F) (df: domain F = I). 
Hypothesis Fmon: forall i j, gle r i j -> sub (Vg F i) (Vg F j).

Definition inl_remark_U := unionb F. 

Definition inl_remark_f :=
  Lg r (fun p => (canonical_injection (Vg F (P p)) (Vg F (Q p)))).

Definition inl_remark_S: inductive_system.
apply(@InductiveSystem F I r inl_remark_f) => //.
- rewrite /inl_remark_f; fprops.
- by rewrite /inl_remark_f; aw.
- rewrite /inl_remark_f => p pr; rewrite LgV//; apply:ci_fp.
  by apply: Fmon; rewrite/gle/related (proj31 or _ pr).
- move => i j k lij ljk; move: (proj33 or _ _ _ lij ljk)=> lik.
  rewrite  /inl_remark_f ! LgV//; aw.
  apply:(ci_compose (Fmon lij) (Fmon ljk)).
- move => i iI.
  have lii: gle r i i by apply:(proj32 or); rewrite sr.
  by rewrite/inl_remark_f LgV//; aw.
Defined.

Lemma inl_remark_S_prop:
   inductive_system_on  inl_remark_S  F I r inl_remark_f.
Proof.  by []. Qed.

Definition inl_remark_ui :=
  Lg I (fun i => canonical_injection (Vg F i)  inl_remark_U).

Lemma inl_remark_sub i: inc i I ->  sub (Vg F i) inl_remark_U.
Proof. move => iI  t tx; apply/setUb_P; rewrite df; ex_tac. Qed.
  
Lemma inl_remark_compat: inl_map_compat inl_remark_S inl_remark_ui inl_remark_U.
Proof.
rewrite /inl_remark_ui; split; aww.
 move => i iI; rewrite LgV//;  apply:(ci_fp (inl_remark_sub iI)).
move => i j /= leij.
move:(arg1_sr leij) (arg2_sr leij); rewrite sr => iI jI; rewrite ! LgV//; aw.
by apply:(ci_compose (@Fmon _ _ leij) (inl_remark_sub jI)).
Qed.


Lemma inl_remark_bijection:
  bijection_prop (inductive_map inl_remark_S inl_remark_ui inl_remark_U)
     (inductive_limit inl_remark_S) inl_remark_U.
Proof.
have H:=inl_remark_compat.
suff: bijection (inductive_map inl_remark_S inl_remark_ui inl_remark_U).
  by move=>h; split => //; rewrite /inductive_map; aw.
split.
  apply /(inl_map_injective H) => /= i x y iI xFi yFi.
  have ha:= inl_remark_sub iI.
  rewrite/inl_remark_ui ! LgV// !ci_V // => ->; exists i => //.
  by apply: (proj32 or); rewrite sr.
apply/(inl_map_surjective H).
have hb i: inc i I -> Imf (Vg inl_remark_ui i) = (Vg F i).
  by move => iI;rewrite /inl_remark_ui LgV//;apply:ci_image;apply:inl_remark_sub.
set_extens t.
  move/setUb_P; rewrite df; move =>[i iI tf]; apply/setUf_P; exists i => //.
  by rewrite hb.  
move => /setUf_P [i iI]; rewrite (hb _ iI) => tF.
apply/setUb_P; rewrite df; ex_tac.
Qed.
  
End InlRemark.


Definition inl_map2_compat S S' u :=
  [/\ fgraph u, domain u = isI S,
   forall i, inc i (isI S) ->
             function_prop (Vg u i) (Vg (isE  S) i) (Vg (isE S') i) &
   forall i j, gle (isr S) i j ->
     Vg (isf S') (J i j) \co Vg u i =  Vg u j \co Vg (isf S) (J i j) ].

Definition inl_map2_property S S' u g :=
  function_prop g  (inductive_limit S)  (inductive_limit S')
  /\ forall i,  inc i (isI S) -> 
    (inl_can_fun S' i) \co (Vg u i) = g \co (inl_can_fun S) i.

Definition inl_map2_aux S u := 
  Lg (isI S) (fun i =>  (inl_can_fun S i) \co (Vg u i)).

Lemma inl_map2_compat_prop0 S S' u x i j:
  inl_same_index S S' ->  inl_map2_compat S S' u ->
  inc x (Vg (isE S) i) ->  gle (isr S) i j ->
  Vf (Vg (isf S') (J i j)) (Vf (Vg u i) x) =
  Vf (Vg u j) (Vf (Vg (isf S) (J i j)) x).
Proof.
move => ha [hb1 hb2 hb3 hb4] xe lij.
move: (inl_prop0 lij) => [iI jI].
have lij':  gle (isr S') i j by rewrite - ha.
move: (hb3 _ iI) => [fui sui tui].
move: (hb3 _ jI) => [fuj suj tuj].
move: (inl_prop4 lij) => [fij sij tij].
move: (inl_prop4 lij') => [fij' sij' tij'].
have co1: Vg u j \coP Vg (isf S) (J i j) by split => //; ue.
have co2: Vg (isf S') (J i j) \coP Vg u i by split => //; ue.
have xs1: inc x (source (Vg u i)) by ue.
have xs2: inc x (source (Vg (isf S) (J i j))) by ue.
move: (f_equal (Vf ^~x) (hb4 _ _ lij)); rewrite ! compfV//.
Qed.

Lemma inl_map2_compat_prop1 S S' u x i j:
  inl_same_index S S' ->  inl_map2_compat S S' u ->
  inc x (Vg (isE S) i) ->  gle (isr S) i j ->
  class (inl_equiv S') (J (Vf (Vg u i) x) i) =
  class (inl_equiv S') (J (Vf (Vg u j) (Vf (Vg (isf S) (J i j)) x)) j).
Proof.
move => ha hb xE lij.
rewrite - (inl_map2_compat_prop0 ha hb xE lij).
move: (proj43 hb  _(proj1 (inl_prop0 lij))) =>[fui sui tui].
rewrite ha in lij; rewrite(inl_class_of_fij lij)//; Wtac.
Qed.

Lemma inl_map2_prop1 S S' u: 
  inl_same_index S S' ->  inl_map2_compat S S' u ->
  inl_map_compat S (inl_map2_aux S' u) (inductive_limit S').
Proof.
move => pa pb; move: (pb) => [pd pe pf pg]. 
have ha:= (inl_same_index_same_I pa).
rewrite /inl_map2_aux; split; aww.
  rewrite - ha;move => i iI; rewrite LgV//.
  move:(pf _ iI) => [fui sui tui]. 
  rewrite ha in iI.
  move:(inl_can_fun_fp iI) => [fp sp tp].
  by saw; fct_tac; rewrite tui.
move => i j le1.
case: (inl_prop0 le1) => iI jI.
move:(inl_prop4 le1) => [fij sij tij].
move:(pf _ iI) (pf _ jI) => [fui sui tui][fuj suj tuj].
rewrite ha  in iI jI.
move:(inl_can_fun_fp iI) (inl_can_fun_fp jI) => [fci sci tci][fcj scj tcj].
have co1: inl_can_fun S' i \coP Vg u i by split => //; ue.
have co2: inl_can_fun S' j \coP Vg u j by split => //; ue.
have ffj: function(inl_can_fun S' j \co Vg u j) by apply: compf_f.
have co3:(inl_can_fun S' j \co Vg u j) \coP Vg (isf S) (J i j).
   split => //; aw; ue.
rewrite !LgV//; apply:function_exten.
- by apply: compf_f.
- by apply: compf_f.
- aw; ue.
- aw; ue.
- aw; rewrite sij  => x xE /=.
  have xe1: inc x (source (Vg u i)) by ue.
  have xe2: inc x (source (Vg (isf S) (J i j))) by ue.
  have xe3: inc (Vf (Vg (isf S) (J i j)) x) (source (Vg u j)).
    by rewrite suj; Wtac.
  have xe4:inc(Vf (Vg u j) (Vf (Vg (isf S) (J i j)) x)) (Vg (isE S') j) by Wtac.
  have xe5: inc (Vf (Vg u i) x) (Vg (isE S') i) by Wtac.
  rewrite ! compfV//.
  rewrite (inl_can_fun_ev jI xe4) (inl_can_fun_ev iI xe5).
  symmetry; apply: (inl_map2_compat_prop1 pa pb xE le1).
Qed.

Definition inductive_limit_fun S S' u :=
  inductive_map S (inl_map2_aux S' u) (inductive_limit S').

Lemma inl_map2_prop S S' u (g := inductive_limit_fun S S' u):
  inl_same_index S S' ->  inl_map2_compat S S' u ->
  inl_map2_property S S' u g.
Proof.
move => ha hb.
move: (inl_map_prop (inl_map2_prop1 ha hb)) => [qa qb]. 
split => // i iI.
move:(iI); rewrite  (inl_same_index_same_I ha)=> iI'.
have idx: inc i (domain (inl_map2_aux S' u)) by rewrite /inl_map2_aux Lgd.
rewrite - qb // /inl_map2_aux LgV//.
Qed.

(* ca sert ? *)
Lemma  inl_map2_prop2 S  u i t:
  inc i (isI S) -> inc t (source (Vg u i)) ->
  function (Vg u i) ->  target (Vg u i) = Vg (isE S) i ->
  Vf (Vg (inl_map2_aux S u) i) t = class (inl_equiv S) (J (Vf (Vg u i) t) i). 
Proof.
move => iI tlim  fu su.
move: (inl_can_fun_fp iI) => [fc sc tc].
have hh:(inl_can_fun S i \coP Vg u i) by  split => //; ue.
rewrite /inl_map2_aux LgV// compfV// inl_can_fun_ev //; Wtac.
Qed.

Lemma inl_map2_unique  S S' u g g':
  inl_same_index S S' ->  inl_map2_compat S S' u->
  inl_map2_property S S' u g ->  inl_map2_property S S' u  g' -> g = g'.
Proof.
move => ha hb.
move: (inl_map2_prop1 ha hb); rewrite /inl_map2_aux; set v := Lg _ _ =>  he.
move => [g1 g2] [g3 g4].
have II:= (inl_same_index_same_I ha); rewrite II in g2 g4.
have dv: domain v = (isI S') by rewrite /v; aw.
have hu1: inl_map_property S v (inductive_limit S') g.
  split => // i idv; have ii: inc i (isI S') by ue.
  by rewrite - g2 // /v LgV//. 
have hu2: inl_map_property S v (inductive_limit S') g'.
  split => // i idv;  have ii: inc i (isI S') by ue.
  rewrite - g4 // /v LgV//.
exact:(inl_map_unique  he hu1 hu2).
Qed.


Lemma inl_inductive_limit_fun_IV2 S1 S2 x S1' S2' x':
  inl_same_data S1 S1' ->  inl_same_data S2 S2' -> x = x' ->
  inductive_limit_fun S1 S2 x = inductive_limit_fun S1' S2' x'.
Proof.
move => ha hb hc.
rewrite /inductive_limit_fun -hc -(inductive_limit_Iv hb).
have si2: (isI S2) = (isI S2') by rewrite -!is_substrate_r; case: hb => _ -> _.
have <-: (inl_map2_aux S2 x) = (inl_map2_aux S2' x).
   rewrite /inl_map2_aux - si2; apply: Lg_exten => i ii.
   by rewrite (inl_can_fun_Iv i hb).
by rewrite /inductive_map -(inductive_limit_Iv ha) /inl_map_val. 
Qed.


Lemma inl_map_val_aux2 S S' u i x (f := inductive_limit_fun S S' u) :
  inl_same_index S S' -> inl_map2_compat S S' u ->
  inc i (isI S) ->  inc x (Vg (isE S) i) ->
  Vf f (class (inl_equiv S) (J x i)) =
  class (inl_equiv S') (J  (Vf (Vg u i) x) i).
Proof.
move => hb ha iI xE.
move:(ha) => [hu1 hu2 hu3 hu4].
move:(inl_map2_prop1 hb ha) => hc.
have II:= (inl_same_index_same_I hb).
have iI': inc i (isI S') by ue.
move: (hu3 _ iI) => [fu su tu].
have uiE: inc (Vf (Vg u i) x) (Vg (isE S') i) by Wtac.
have xE': inc x (source (Vg u i)) by ue.
have cop:inl_can_fun S' i \coP Vg u i.
  by move:(inl_can_fun_fp iI') => [fc sc tc]; split => //; ue.
rewrite /f/inductive_limit_fun (inl_inductive_map_ev hc iI xE)/inl_map2_aux.
by rewrite LgV// compfV// inl_can_fun_ev.
Qed.

Lemma inl_map2_prop3 S S' u (f := inductive_limit_fun S S' u):
  inl_same_index S S' -> inl_map2_compat S S' u ->
  function_prop f (inductive_limit S)  (inductive_limit S') /\
  forall i x,
  inc i (isI S) ->  inc x (Vg (isE S) i) ->
  Vf f (class (inl_equiv S) (J x i)) =
  class (inl_equiv S') (J  (Vf (Vg u i) x) i).
Proof.
move => Ha Hu; split. 
  exact: (proj1 (inl_map2_prop Ha Hu)).
move=> i x ii xx; exact: (inl_map_val_aux2 Ha Hu ii xx).
Qed.  


Lemma inl_map2_compose S S' S'' u v (F := inductive_limit_fun)
  (w:= Lg (isI S) (fun i => (Vg v i) \co (Vg u i))) :
  inl_same_index S S' ->  inl_same_index S' S'' ->
  inl_map2_compat S S' u -> inl_map2_compat S' S'' v ->
  inl_map2_compat S S'' w /\
  F S S'' w = F S' S'' v \co F S S' u.
Proof.
move => sb1 sb2 hu hv.
have sb3: inl_same_index S S'' by  rewrite /inl_same_index sb1.
move:(inl_map2_prop sb1 hu); rewrite -/F => pa1.
move:(inl_map2_prop sb2 hv); rewrite -/F => pa2.
move: hu hv=> [cpa1 cpa2 cpa3 cpa4]  [cpb1 cpb2 cpb3 cpb4]. 
have ssI:= inl_same_index_same_I sb1.
rewrite - ssI in cpb3.
have ha i: inc i (isI S) ->  Vg v i \coP Vg u i.
    move => iI.
    move: (cpa3 _ iI)  (cpb3 _ iI) =>[fu su tu] [fv sv tv].
    by split => //;rewrite sv tu.
have hb i j: gle (isr S) i j -> Vg u j \coP Vg (isf S) (J i j).
  move => lij.
  move:(is_function_f lij)(proj2(inl_prop0 lij)) => [ff sf tf] /cpa3 [fu su tu].
  by split => //; rewrite su tf; aw.
have hb' i j: gle (isr S') i j -> Vg v j \coP Vg (isf S') (J i j).
  move => lij; move:(lij); rewrite - sb1 => lij'.
  move:(is_function_f lij) (cpb3 _ (proj2 (inl_prop0 lij'))). 
  move => [ff sf tf] [fu su tu].
  by split => //; rewrite su tf; aw.
have hc i j:  gle (isr S) i j -> Vg (isf S') (J i j) \coP Vg u i.
  move => lij;  move:(lij); rewrite sb1 => lij'.
  move:(is_function_f lij') (proj1(inl_prop0 lij))=> [ff sf tf] /cpa3[fu su tu].
  by split => //; rewrite sf tu; aw.
have hc' i j: gle (isr S) i j ->  Vg (isf S'') (J i j) \coP Vg v i.
  move => lij; move:(lij); rewrite sb1 sb2 => lij'.
  move: (proj1(inl_prop0 lij))(is_function_f lij')=>/cpb3[fu su tu] [ff sf tf].
  by split => //; rewrite sf tu; aw.
have cpc:inl_map2_compat S S'' w.
  rewrite /w; split; aww.
    move => i iI; rewrite LgV//.
    move:(cpa3 _ iI) (cpb3 _ iI) => [fu su tu] [fv sv tv].
    by saw;fct_tac; rewrite sv tu.
  move => i j lij.
  have lij': gle (isr S') i j by rewrite - sb1.
  move:(inl_prop0 lij)=> [isr jsr]; rewrite ! LgV//.
  rewrite - (compfA (ha _ jsr) (hb _ _ lij)) - (cpa4 _ _ lij).
  rewrite (compfA (hb' _ _ lij') (hc _ _ lij))  - (cpb4 _ _ lij').
  by rewrite (compfA (hc' _ _ lij) (ha _ isr)).
split; first exact.
apply:(inl_map2_unique sb3 cpc (inl_map2_prop sb3 cpc)).
move: pa1 pa2=> [[ff sf tf] ra2] [ [ff' sf' tf'] ra4].
have ra3: F S' S'' v \coP F S S' u by split => //; rewrite sf' tf.
split; first by saw; apply: compf_f.
move => i iI.
have ssI':= inl_same_index_same_I sb3.
have iI': inc i (isI S') by rewrite - ssI. 
have iI'': inc i (isI S'') by rewrite - ssI'. 
move: (inl_can_fun_fp iI'') => [fpl'' spl'' tpl''].
move: (inl_can_fun_fp iI') =>  [fpl' spl' tpl'].
move: (inl_can_fun_fp iI) =>  [fpl spl tpl].
move: (cpb3 _ iI) => [fv sv tv].
move: (cpa3 _ iI) => [fu su tu].
have qa: F S S' u \coP inl_can_fun S i by split => //; ue.
have qb: F S' S'' v \coP inl_can_fun S' i by split => //;ue.
have qc: inl_can_fun S' i \coP Vg u i by split => //; ue.
have qd: inl_can_fun S'' i \coP Vg v i by split => //; ue.
rewrite - (compfA ra3 qa) -(ra2  _ iI) (compfA qb qc) - (ra4 _ iI').
rewrite -(compfA qd (ha _ iI)) /w LgV//.
Qed.

Lemma inl_limit_fun_inj S S' u:
  inl_same_index S S' -> inl_map2_compat S S' u ->
  (forall i, inc i (isI S) ->   injection (Vg u i)) ->
  injection (inductive_limit_fun S S' u).
Proof.
move => ha hb hc.
have II:= (inl_same_index_same_I ha).
move:(inl_map2_prop ha hb) => [[ff sf tf] etc].
move: (hb) => [hb1 hb2 hb3 hb4].
split => //; rewrite sf => x y xs ys.
move/inductive_limit_hi: xs => [Qrx Prx ->].
move/inductive_limit_hi: ys => [Qry Pry ->].
rewrite (inl_map_val_aux2 ha hb Qrx Prx) (inl_map_val_aux2 ha hb Qry Pry).
set xx := (Vf (Vg u (Q (rep x))) _).
set yy := (Vf (Vg u (Q (rep y))) _).
have xxE: inc xx (Vg (isE S') (Q (rep x))).
  rewrite /xx;move:(hb3 _ Qrx) => [ff' sf' tf']; Wtac.
have yyE: inc yy (Vg (isE S') (Q (rep y))).
  rewrite /yy;move:(hb3 _ Qry) => [ff' sf' tf']; Wtac.
rewrite II in Qrx Qry.
move/(inl_class_eq_bis Qrx Qry xxE yyE) => [k []]; aw; rewrite - ha => lik ljk.
rewrite (inl_map2_compat_prop0  ha hb Prx lik).
rewrite (inl_map2_compat_prop0  ha hb Pry ljk). 
rewrite - (inl_class_of_fij lik Prx) - (inl_class_of_fij ljk Pry).
have kI := (proj2(inl_prop0 lik)).
move:(inl_prop4 lik) => [fij sik tik].
move:(inl_prop4 ljk) => [fjj sjk tjk].
move: (hb3 _ kI) => [fuk suk tuk].
have qg: inc (Vf (Vg (isf S) (J (Q (rep x)) k)) (P (rep x))) (source (Vg u k)).
    rewrite suk. Wtac.
have qh: inc (Vf (Vg (isf S) (J (Q (rep y)) k)) (P (rep y))) (source (Vg u k)).
    rewrite suk; Wtac.
by move/(proj2 (hc _ (proj2(inl_prop0 lik))) _ _ qg qh) => ->.
Qed.

Lemma inl_limit_fun_surj S S' u:
  inl_same_index S S' -> inl_map2_compat S S' u ->
  (forall i, inc i (isI S) -> surjection (Vg u i)) ->
  surjection (inductive_limit_fun S S' u).
Proof.
move => ha hb hc.
move:(inl_map2_prop ha hb) => [[ff sf tf] etc].
split => //; rewrite tf sf => y /(inductive_limitP) [ry ->].
move:ry; rewrite inl_equiv_sr=> qa.
move:(qa)=> /inl_sumP [pry Qry Pry].
have II:= (inl_same_index_same_I ha).
rewrite - II in Qry.
move: (hb) => [hb1 hb2 hb3 hb4].
move:(hb3 _ Qry) => [fui sui tui].
rewrite - tui in Pry.
move:(proj2 (hc _ Qry) _ Pry); rewrite sui; move  =>[x xs xv].
have cc: inc (class (inl_equiv S) (J x (Q (rep y)))) (inductive_limit S).
  by apply:inl_class_in_lim.
by ex_tac; rewrite inl_map_val_aux2 // - xv pry.
Qed.

  
Definition inl_subfam_hyp S M:=
  [/\ fgraph M, domain M = isI S,
   forall i, inc i (isI S) -> sub (Vg M i) (Vg (isE S) i) &
   forall i j, gle (isr S) i j -> 
     sub (Vfs (Vg (isf S) (J i j)) (Vg M i)) (Vg M j) ].

Definition inl_subfam_fct S M :=
  Lg  (isr S) (fun z => restriction2 (Vg (isf S) z) (Vg M (P z)) (Vg M (Q z))).

Lemma inl_subfam_prop1 S M (g := inl_subfam_fct S M):
  inl_subfam_hyp S M ->
  [/\ 
   forall z, inc z (isr S) -> 
      restriction2_axioms (Vg (isf S) z) (Vg M (P z)) (Vg M (Q z)),
   forall i j x, gle (isr S) i j -> inc x (Vg M i) ->
     Vf (Vg g (J i j)) x = Vf (Vg (isf S) (J i j)) x,
   forall i, inc i (isr S)-> function_prop (Vg g i) (Vg M (P i)) (Vg M (Q i)),
   forall i j k, gle (isr S) i j -> gle (isr S) j k ->
                 Vg g (J j k) \co  Vg g (J i j) = Vg g (J i k) &
   forall i, inc i (isI S) -> Vg g (J i i) = identity (Vg M i)].
Proof.
move =>[pa pb pc pd].
have rc z: inc z (isr S) ->
       restriction2_axioms (Vg (isf S) z) (Vg M (P z)) (Vg M (Q z)).
  move => zr.
  move:(is_function_f zr) =>[ff sf tf].
  move: (pr1_sr zr)(pr2_sr zr) => iI jI.
  split.
  - done.
  - by rewrite sf; apply: pc; rewrite -is_substrate_r.
  - by rewrite tf; apply: pc;rewrite -is_substrate_r.
  - have pz:= ((proj31 (is_preorder_r S)) _ zr).
    by rewrite -{1} pz;apply: pd; rewrite/ gle/related pz.
have rd:forall i j x, gle (isr S) i j -> inc x (Vg M i) ->
     Vf (Vg g (J i j)) x = Vf (Vg (isf S) (J i j)) x.
  move => i j x ha hb.
  have hb':inc x (Vg M (P (J i j))) by aw.
  rewrite -(restriction2_V (rc _ ha) hb'); rewrite /g/inl_subfam_fct LgV//.
have re i: inc i (isr S) -> function_prop (Vg g i) (Vg M (P i)) (Vg M (Q i)).
  move => ir; rewrite /g/inl_subfam_fct LgV//.
  exact: (restriction2_prop (rc _ ir)).
have rg i: inc i (isI S) -> Vg g (J i i) = identity (Vg M i).
  move => ii.
  have iiI: inc (J i i) (isr S) by apply: inl_prop1.
  move:(re _ iiI); aw => fh;apply:(identity_prop0 fh) => x xM.
  by rewrite (rd _ _  _ iiI xM) (is_identity_f ii)  idV//; apply: pc.
split => // i j k lij ljk.
have lik: gle (isr S) i k by apply: (proj33 (is_preorder_r S)) lij ljk. 
move: (re _ lij) => [fij sij tij].
move: (re _ ljk) => [fjk sjk tjk].
move: (re _ lik) => [fik sik tik].
rewrite ! pr2_pair in tij tik tjk.
rewrite ! pr1_pair in sij sik sjk.
have co1:  Vg g (J j k) \coP Vg g (J i j) by  split => //; ue.
have fc1: function (Vg g (J j k) \co Vg g (J i j)) by apply: compf_f.
apply: function_exten => //.
- by aw; ue.
- by aw; ue.
aw; rewrite sij => x xM.
have ha: inc x (Vg (isE S) i) by  apply: (pc _ (proj1 (inl_prop0 lij))).
have hb: inc x (source (Vg g (J i j))) by ue.
move:(inl_prop4 lij) => [fa ffb fc].
have : inc (Vf (Vg g (J i j)) x) (Vg M j).
    rewrite - tij; Wtac.
rewrite (rd _ _ _ lij xM) => hd.
have hc: inc x (source (Vg (isf S) (J i j))) by ue.
by rewrite compfV // !rd //  inl_prop3.
Qed.

Definition inductive_system_subsets
           S M (H:inl_subfam_hyp S M) : inductive_system.
Proof.
apply:(@InductiveSystem M (isI S) (isr S) (inl_subfam_fct S M)).
- exact: is_preorder_r.
- by rewrite is_substrate_r.
- exact: is_directed_r.
- by case:H.
- by case:H.
- by rewrite /inl_subfam_fct; fprops.
- by rewrite /inl_subfam_fct; aw.
- by case: (inl_subfam_prop1 H).
- by case: (inl_subfam_prop1 H).
- by case: (inl_subfam_prop1 H).
Defined.

Lemma inl_subsets_prop S  M (H:inl_subfam_hyp S M) :
  inductive_system_on (inductive_system_subsets H)
     M  (isI S)  (isr S) (inl_subfam_fct S M).
Proof.  done. Qed.

Lemma inl_subsets_prop_Iv S M
      (H H':inl_subfam_hyp S M) :
  inl_same_data (inductive_system_subsets H) (inductive_system_subsets H').
Proof.
move:(inl_subsets_prop H) => [ra rb rc rd].
move:(inl_subsets_prop H') => [ra' rb' rc' rd'].
by rewrite /inl_same_data ra rc rd.
Qed.

Lemma inl_subsets_prop_I2v S S' M
      (H:inl_subfam_hyp S M) (H':inl_subfam_hyp S' M) :
  inl_same_data S S' ->
  inl_same_data (inductive_system_subsets H) (inductive_system_subsets H').
Proof.
move:(inl_subsets_prop H) => [ra rb rc rd].
move:(inl_subsets_prop H') => [ra' rb' rc' rd'].
rewrite /inl_same_data ra rc rd ra' rc' rd' => - [ea eb ec].
by rewrite /inl_subfam_fct eb ec.
Qed.

Lemma inl_subfam_compat S M
   (H:inl_subfam_hyp S M) (S' := (inductive_system_subsets H))
   (ji := fun i => canonical_injection (Vg M i) (Vg (isE S) i)):
  inl_map2_compat S' S (Lg (isI S) ji).
Proof.
move: (H) => [ha hb hc hd].
have II: isI S' = isI S by [].
have rr: (isr S') = (isr S) by [].
have he: inl_same_index S S' by [].
split; aww.
  by rewrite /ji;move => i ii; rewrite LgV//; apply:ci_fp; apply: hc; rewrite - II.
move =>  i j lij.
case:(inl_prop0 lij); rewrite II => iI jI; rewrite  LgV// LgV//.
move: (hc _ iI) (hc _ jI) => s1 s2.
move:(ci_fp s1); rewrite-/(ji i); move => [fci sci tci].
move:(ci_fp s2); rewrite-/(ji j); move => [fcj scj tcj].
move:(inl_prop4 lij) => [fij' sij' tij'].
rewrite rr in lij.
move:(inl_prop4 lij) => [fij sij tij].
have co1: Vg (isf S) (J i j) \coP ji i by split => //; ue.
have co2: ji j \coP Vg (isf S') (J i j) by split => //; ue.
apply:function_exten.
  + by apply:compf_f.
  + by apply:compf_f.
  + aw; ue.
  + aw; ue.
  + aw; rewrite sci => x xM.
   have qa: inc x (source (ji i)) by ue.
   have qb: inc x (source (Vg (isf S') (J i j))) by ue.
   have qc: (Vf (Vg (isf S') (J i j)) x)  = Vf (Vg (isf S) (J i j)) x.
     rewrite /=/inl_subfam_fct LgV//; aw; rewrite  restriction2_V //.
     by split => //; try ue; apply: hd. 
   rewrite !compfV// qc/ji !ci_V//; apply: (hd _ _ lij).
   have hf:sub (Vg M i) (source (Vg (isf S) (J i j))) by ue.
   apply/(Vf_image_P fij hf); ex_tac.
Qed.


Lemma inl_subfam_prop3 S M
   (H:inl_subfam_hyp S M) (S' := (inductive_system_subsets H))
   (ji := fun i => canonical_injection (Vg M i) (Vg (isE S) i))
   (u := (inductive_limit_fun S' S (Lg (isI S) ji))):
  forall i x, inc i (isI S) ->  inc x (Vg M i) ->
        Vf u (class (inl_equiv S') (J x i)) =  class (inl_equiv S) (J x i).
Proof.
move => i x iI xE. 
have ha:inl_same_index S' S by [].
have hb:=  inl_subfam_compat H.
move:(inl_map_val_aux2 ha hb iI xE); rewrite LgV// -/u ci_V //.
by move: (H) => [_ _ hc _]; apply: hc.
Qed.

Lemma inl_subfam_prop4 S M
      (H:inl_subfam_hyp S M) (S' := (inductive_system_subsets H))
      (ji := fun i => canonical_injection (Vg M i) (Vg (isE S) i)):
      injection_prop (inductive_limit_fun S' S (Lg (isI S) ji))
                     (inductive_limit S') (inductive_limit S).
Proof.
have II: isI S' = isI S by [].
move: (inl_subfam_compat H) => cc.
move: (H) => [ha hb hc hd].
rewrite/inductive_limit_fun /inductive_map; saw.
apply:inl_limit_fun_inj => // i; rewrite II => iI; rewrite LgV//; apply:ci_fi; fprops.
Qed.

Section InductiveLimitCorollary.

Variables S S': inductive_system.
Variable u: Set.
Hypothesis sii:inl_same_index S S'.
Hypothesis m2c: inl_map2_compat S S' u.



Section InductiveLimitCorollary1.

Variable M: Set.
Hypothesis Mhyp: inl_subfam_hyp S M.

Definition inl_p7c1_M' :=
  Lg (isI S) (fun i => Vfs (Vg u i) (Vg M i)).

Lemma inl_sub_fam_im1: inl_subfam_hyp S' inl_p7c1_M'.
Proof.
have II:= (inl_same_index_same_I sii).
move: m2c => [ha hb hc hd].
move: Mhyp => [qa qb qc qd].
rewrite /inl_p7c1_M'; split; aww.
  rewrite - II => i iI; rewrite LgV//.
  move: (hc _ iI) => [fui sui tui].
  rewrite - tui; apply:(fun_image_Starget1 fui).
rewrite - sii => i j lij; move:(inl_prop0 lij) => [iI jI]; rewrite !LgV//.
move => t.
move: (hc _ iI) => [fui sui tui].
move: (hc _ jI) => [fuj suj tuj].
move:(hd _ _ lij) (qd _ _ lij)  => hd' qd'.
move:(inl_prop4 lij) => [fij sij tij].
rewrite sii in lij.
move:(inl_prop4 lij) => [fij' sij' tij'].
have pa: sub (Vfs (Vg u i) (Vg M i)) (source (Vg (isf S') (J i j))).
  rewrite sij' - tui; apply:(fun_image_Starget1 fui).
have pb: sub (Vg M j) (source (Vg u j)) by rewrite suj; apply: qc.
have pc: sub (Vg M i) (source (Vg u i)) by rewrite sui; apply: qc.
move/(Vf_image_P fij' pa) => [v /(Vf_image_P fui pc) [w wa ->]  ->].
have co1: Vg u j \coP Vg (isf S) (J i j) by split => //;ue.
have co2: Vg (isf S') (J i j) \coP Vg u i by split => //; ue.
have ws0: inc w (source (Vg u i)) by apply: pc.
have ws1:inc w (source (Vg (isf S) (J i j))) by rewrite sij - sui.
have pc':sub (Vg M i) (source (Vg (isf S) (J i j))) by ue.
have ws2: inc (Vf (Vg (isf S) (J i j)) w) (Vg M j).
  apply:qd'; apply/(Vf_image_P fij pc'); ex_tac.
move:(f_equal (Vf^~w) hd'); rewrite ! compfV //; move ->.
apply/(Vf_image_P fuj pb); ex_tac.
Qed.


Definition inl_p7c1_MS :=  inductive_system_subsets Mhyp.
Definition inl_p7c1_MS' := inductive_system_subsets  inl_sub_fam_im1.

Definition inl_p7c1_ji := 
 Lg (isI S)( fun i => canonical_injection (Vg M i) (Vg (isE S) i)).

Definition inl_p7c1_ji' := 
 Lg (isI S')( fun i => canonical_injection (Vg inl_p7c1_M' i) (Vg (isE S') i)).

Definition inl_p7c1_ji_lim := inductive_limit_fun inl_p7c1_MS S inl_p7c1_ji.
Definition inl_p7c1_ji_lim' := inductive_limit_fun inl_p7c1_MS' S' inl_p7c1_ji'.

Lemma inl_p7c1_ji_prop :
 injection_prop  inl_p7c1_ji_lim 
 (inductive_limit  inl_p7c1_MS) (inductive_limit S).
Proof. by apply: inl_subfam_prop4.  Qed.

Lemma inl_p7c1_ji'_prop :
 injection_prop inl_p7c1_ji_lim' 
 (inductive_limit inl_p7c1_MS') (inductive_limit S').
Proof. apply:inl_subfam_prop4. Qed.


Lemma inl_prop7_cor_i:
  Imf inl_p7c1_ji_lim' = Vfs (inductive_limit_fun S S' u) (Imf inl_p7c1_ji_lim).
Proof.
move: inl_p7c1_ji_prop => [[fci _] sci tci].
move: inl_p7c1_ji'_prop => [[fci' _] sci' tci'].
have II:= (inl_same_index_same_I sii).
move:(inl_map2_prop sii m2c); set uu := (inductive_limit_fun S S' u). 
move =>[ [fuu suu tuu] uup].
have ha:sub (Imf inl_p7c1_ji_lim) (source uu).
  move => t/(Imf_P fci); rewrite sci suu.
  move => [v/inductive_limit_hi /= [Qi Pm ->] ->].
  rewrite (inl_subfam_prop3 _ Qi Pm).
  by apply:inl_class_in_lim => //; apply:(proj43 Mhyp _ Qi).
move:m2c => [fgu du up1 up2].
set_extens t.
  move/(Imf_P fci'); rewrite sci'.
  move => [v /inductive_limit_hi /= [Qi' Pm ->] ->].
  rewrite (inl_subfam_prop3 _ Qi' Pm).
  have Qi:inc (Q (rep v)) (isI S) by rewrite II.
  move: Pm; rewrite /inl_p7c1_M' LgV//.
  move:(up1 _ Qi) => [fui sui tui].
  have hb: sub (Vg M (Q (rep v))) (source (Vg u (Q (rep v)))). 
     rewrite sui; apply: (proj43 Mhyp _ Qi).
  move/(Vf_image_P fui hb) => [y yM ->].
  rewrite -(inl_map_val_aux2 sii m2c Qi ((proj43 Mhyp _ Qi) _ yM)).
  have hc: inc (class (inl_equiv S) (J y (Q (rep v))))
               (Imf inl_p7c1_ji_lim).
    apply /(Imf_P fci); rewrite sci.
    exists (class (inl_equiv inl_p7c1_MS) (J y (Q (rep v)))).
      by apply:inl_class_in_lim. 
    by rewrite inl_subfam_prop3.
  apply/(Vf_image_P fuu ha); ex_tac.
move/(Vf_image_P fuu ha) => [v /(Imf_P fci)]; rewrite sci.
move => [w /inductive_limit_hi /= [Qi Pcv ->] ->]. 
have hb: inc (P (rep w)) (Vg (isE S) (Q (rep w))).
  by apply: (proj43 Mhyp _ Qi).
rewrite (inl_subfam_prop3  _ Qi Pcv) inl_map_val_aux2 // => ->.
apply/(Imf_P fci'); rewrite sci'.
have Qi': inc (Q (rep w)) (isI S') by ue.
move:(up1 _ Qi) => [fu su tu].
set y := (Vf (Vg u (Q (rep w))) (P (rep w))).
have hc:sub (Vg M (Q (rep w))) (source (Vg u (Q (rep w)))).
   rewrite su; apply:(proj43 Mhyp _ Qi).
have yc: inc y (Vg inl_p7c1_M' (Q (rep w))).
  rewrite /inl_p7c1_M' LgV//; apply/(Vf_image_P fu hc); ex_tac.
exists  (class (inl_equiv inl_p7c1_MS') (J y (Q (rep w)))).
  apply: inl_class_in_lim => //=.
by rewrite inl_subfam_prop3.
Qed.


End InductiveLimitCorollary1.

  
Definition inl_inv_image_compat Mi:=
  [/\ fgraph Mi,
   domain Mi = isI S',
   forall i, inc i (isI S') -> sub (Vg Mi i) (Vg (isE S') i) &
   forall p, inc p (isr S') ->
          sub (Vfs (Vg (isf S') p)(Vg Mi (P p))) (Vg Mi (Q p))].

Lemma inl_sub_fam_im2 Mi
  (Mi' := Lg (isI S) (fun i => Vfi (Vg u i) (Vg Mi i))):
  inl_inv_image_compat Mi ->
  inl_subfam_hyp S Mi'.
Proof.
move:m2c => [ha hb hc hd] [qa qb qc qd]. 
have II:= (inl_same_index_same_I sii).
rewrite/Mi'; split => //; fprops; aw;  trivial.
  move => i iI;rewrite LgV//.
  move: (hc _ iI) => [fu su tu]; rewrite - su; apply:(sub_inv_im_source fu).
  by rewrite tu; apply: qc; rewrite - II.
move => i j lij.
move:(inl_prop0 lij) => [iI jI]; rewrite !LgV//.
move => t.
move: (hc _ iI) => [fui sui tui].
move: (hc _ jI) => [fuj suj tuj].
move:(inl_prop4 lij) => [fij sij tij].
rewrite - II in qc.
have pa:sub (Vfi (Vg u i) (Vg Mi i)) (source (Vg (isf S) (J i j))).
  rewrite sij - sui; apply:(sub_inv_im_source fui); rewrite tui;  fprops.
move/(Vf_image_P fij pa) => [v /iim_fun_P [w wa wb] ->].
move:(hd _ _ lij) => hd'.
rewrite sii in lij; move:(qd _  lij); aw => eqa.
move:(inl_prop4 lij) => [fij' sij' tij'].
have pb:sub (Vg Mi i) (source (Vg (isf S') (J i j))) by rewrite sij'; apply: qc.
have pc:inc (Vf (Vg (isf S') (J i j)) w)  (Vg Mi j).
  apply: eqa; apply/(Vf_image_P fij' pb); ex_tac.
move:(p1graph_source fui wb); rewrite sui => pd.
have aa :gle (isr S) i j by rewrite sii.
apply/iim_fun_P; ex_tac.
move:(inl_map2_compat_prop0 sii m2c pd aa); rewrite (Vf_pr fui wb) => ->.
apply: (Vf_pr3 fuj);rewrite suj; Wtac.
Qed.
  
Definition inl_inv_image_compat1 ai:=
  [/\ fgraph ai,
   domain ai = isI S',
   forall i, inc i (isI S') -> inc (Vg ai i) (Vg (isE S') i) &
   forall p, inc p (isr S') -> Vf (Vg (isf S') p)(Vg ai (P p)) = (Vg ai (Q p))].

Section InductiveLimitCorollary2.

Variable a_fam: Set.
Hypothesis a_fam_prop:  inl_inv_image_compat1 a_fam.

Definition inl_p7c2_Ni :=
   Lg (isI S) (fun i => Vfi1 (Vg u i) (Vg a_fam i)).

Definition inl_p7c2_ci :=
  Lg (isI S) (fun i => canonical_injection (Vg inl_p7c2_Ni i) (Vg (isE S) i)).

Lemma inl_sub_fam_im3: inl_subfam_hyp S inl_p7c2_Ni.
Proof.
move: a_fam_prop => [ha hb hc hd].
set Mi := Lg (isI S) (fun i =>  (singleton (Vg a_fam i))).
have ->: inl_p7c2_Ni
    =  Lg (isI S) (fun i => Vfi (Vg u i) (Vg Mi i)).
   apply: Lg_exten => i iS; rewrite /Mi LgV//.
have II:= (inl_same_index_same_I sii).
rewrite/Mi; apply: inl_sub_fam_im2; split; aww.
  move => i iI t; rewrite LgV; [  by move/set1_P ->; apply: hc | ue].
move => p pr.
move:(proj31 (is_preorder_r S') _ pr) => pp.
move:(pr); rewrite -{1} pp => /inl_prop0; rewrite - II; move => [iI jI].
move: (is_function_f pr) => [fi si ti].
have xa: inc (Vg a_fam (P p)) (source (Vg (isf S') p)).
  by rewrite si; apply: hc; rewrite - II.
by rewrite ! LgV// (fun_image_set1 fi xa) (hd _ pr).
Qed.

Lemma inl_sub_fam_im3_val: 
  forall i, inc i (isI S) ->  
    class (inl_equiv S') (J (Vg a_fam i) i)
    = class (inl_equiv S') (J (Vg a_fam (rep (isI S))) (rep (isI S))).
Proof.
move: a_fam_prop=> [ha hb hc hd]. 
have II:= (inl_same_index_same_I sii).
pose ci i := class (inl_equiv S') (J (Vg a_fam i) i).
have h: forall i j, gle (isr S') i j ->  ci i = ci j.
  move => i j lij.
  move: (inl_class_of_fij lij  (hc _ (proj1 (inl_prop0 lij)))).
  by move:(hd _ lij); aw; move => ->.
rewrite II => i iI.
have rI: inc (rep (isI S')) (isI S') by apply:rep_i; ex_tac.
move:(is_directed_r iI rI) => [k [kI ka kb]].
by rewrite -/(ci i ) (h _ _ ka) -(h _ _ kb). 
Qed.

Definition inl_p7c2_S'' := (inductive_system_subsets inl_sub_fam_im3).
Definition inl_p7c2_ip := inductive_limit_fun inl_p7c2_S'' S inl_p7c2_ci.

Lemma inl_sub_fam_im4:
  injection_prop inl_p7c2_ip (inductive_limit inl_p7c2_S'') (inductive_limit S).
Proof. by move: (inl_subfam_prop4 (inl_sub_fam_im3)). Qed.
    
Lemma inl_prop7_cor_ii
      (a := class (inl_equiv S') (J (Vg a_fam (rep (isI S))) (rep (isI S)))):
  Imf inl_p7c2_ip = Vfi1 (inductive_limit_fun S S' u)  a.
Proof.
move:(inl_map2_prop sii m2c); set uu := (inductive_limit_fun S S' u). 
move =>[ [fuu suu tuu] uup].
have II:= (inl_same_index_same_I sii).
set Nip:=(inl_sub_fam_im3).
move: (inl_sub_fam_im4) => [[fi _] si ti].
move:(a_fam_prop) => [Ha Hb Hc Hd].
set_extens t.
  move/(Imf_P fi); rewrite si; move => [v va ->].
  apply(iim_fun_set1_P _ fuu); rewrite suu.
  move/inductive_limit_hi: va => /=  [Qr Pr ->].
  rewrite (inl_subfam_prop3 inl_sub_fam_im3 Qr Pr).
  move: Pr; rewrite /inl_p7c2_Ni LgV//.
  move:(proj43 m2c _ Qr) => [fui sui tui].
  move/(iim_fun_set1_P _ fui); rewrite sui; move => [ha hb].
  split; first  by apply: inl_class_in_lim.
  by rewrite (inl_map_val_aux2 sii m2c Qr ha)  /a -(inl_sub_fam_im3_val Qr) hb.
move/(iim_fun_set1_P _ fuu);rewrite suu.
move => [/inductive_limit_hi [Qr Pr ->]].
move:(Qr); rewrite II => Qr'.
have pa: inc (Vg a_fam (Q (rep t))) (Vg (isE S') (Q (rep t))) by apply: Hc.
have pb: inc (Vf (Vg u (Q (rep t))) (P (rep t))) (Vg (isE S') (Q (rep t))).
  move:(proj43 m2c _ Qr) => [fui sui tui]; Wtac.
rewrite (inl_map_val_aux2 sii m2c Qr Pr).
rewrite /a -(inl_sub_fam_im3_val Qr).
move/ (inl_class_eq_bis Qr' Qr' pa pb) => [j [_]]; aw => lij.
move: (Hd _ lij); aw => ->; rewrite  - sii in lij.
rewrite (inl_map2_compat_prop0 sii m2c Pr lij).
set y := Vf (Vg (isf S) (J (Q (rep t)) j)) (P (rep t)) => ya.
move:(proj2 (inl_prop0 lij)) => jI.
move:(proj43 m2c _ jI) => [fui sui tui].
have yNi: inc y (Vg inl_p7c2_Ni j).
   rewrite /y /inl_p7c2_Ni LgV//; apply/(iim_fun_set1_P _ fui); split => //.
   move: (inl_prop4 lij) => [fij sij tij]; rewrite sui; Wtac.
rewrite -(inl_class_of_fij lij Pr).
rewrite -(inl_subfam_prop3 inl_sub_fam_im3 jI yNi).
apply/(Imf_P fi).
exists (class (inl_equiv (inl_p7c2_S'')) (J y j)) => //;rewrite si.
by apply:inl_class_in_lim.
Qed.

End InductiveLimitCorollary2. 
End InductiveLimitCorollary. 


Section InlPrl_R2.

Variables (S: inductive_system) (u E': Set).
Hypothesis mcu: inl_map_compat S u E'.

Definition inl_rem2_S' := Injex2_system E' (is_preorder_r S)
                                        (is_substrate_r S) (@is_directed_r S).

Lemma inl_rem2_prop1: inl_map2_compat S inl_rem2_S' u.
Proof.
move: mcu => [ha hb hc hd].
split => //; first by  move => i iI; simpl; rewrite LgV//; apply: hc.
move => i j lij; move:(hd _ _ lij) => /= ->; rewrite LgV//.
by move/hc:(proj1 (inl_prop0 lij)) => [fui _ <-]; apply: compf_id_l.    
Qed.

Lemma inl_rem2_prop2 (u1 := inductive_map S u E')
      (u2:= inductive_limit_fun S  inl_rem2_S' u)
      (can := Lf (fun z => (P (rep z))) (inductive_limit inl_rem2_S') E'):
  nonempty (isI S) ->
  can \coP u2 /\ u1 = can \co u2.
Proof.
move => nei.
move: (Inj_ex2_can_fun E' (is_preorder_r S)
    (is_substrate_r S) (@is_directed_r S) nei).
rewrite -/can -/inl_rem2_S'; move => [bf sf tf].
move:(inl_map_prop mcu); rewrite -/u1; move =>[[fu1 su1 tu1] u1p].
have ha: inl_same_index S inl_rem2_S' by [].
have cc:=  inl_rem2_prop1.
move:(inl_map2_prop ha cc);rewrite -/u2; move =>[[fu2 su2 tu2] u2p].
have cop: can \coP u2  by split; [ fct_tac | done | ue].
have ax:lf_axiom (fun z => P (rep z)) (inductive_limit inl_rem2_S') E'.
  by move => t /inductive_limit_hi /= [qa qb _]; move:qb; rewrite LgV//.
split => //.
apply: function_exten; [ exact | fct_tac | aw; ue | aw; ue | ].
rewrite su1 => x xs.
have xu2: inc x (source u2) by ue.
have u2x: inc (Vf u2 x) (inductive_limit inl_rem2_S') by Wtac.
rewrite /can compfV// LfV //.
move/inductive_limit_hi: xs => [pa pb pc].
rewrite pc /u1 inl_inductive_map_ev // inl_map_val_aux2 //.
set w := Vf (Vg u (Q (rep x))) (P (rep x)).
move: (proj43 mcu _ pa) => [fui sui tui].
have qa: inc (J w (Q (rep x))) (substrate (inl_equiv inl_rem2_S')).
  rewrite inl_equiv_sr; apply/inl_sumP;split;aww.
  rewrite LgV  ///w; Wtac.
move: (related_rep_class (proj1 (inl_equiv_esr inl_rem2_S')) qa).
by move/Inj_ex2_can_prop => [_ _]; aw.
Qed.

End InlPrl_R2.

Definition sub_right_directed J r :=
   sub J (substrate r) /\ (right_directed_on r J).

Definition inl_restr S J (H:sub_right_directed J(isr S)) : inductive_system.
Proof.
apply:(@InductiveSystem (restr (isE S) J) J (induced_order (isr S) J)
  (restr (isf S) (induced_order (isr S) J))).
- exact:(iorder_preorder (proj1 H) (is_preorder_r S)).
- exact:(ipreorder_sr(is_preorder_r S)  (proj1 H) ).
- exact:(right_directed_ind_prop (is_preorder_r S)  (proj1 H) (proj2 H)).
- fprops.
- by aw.
- fprops.
- by aw.
- move => p po; move: (po) => /setI2_P [pa /setX_P [pp pI qI]].
  by rewrite ! LgV//; apply:is_function_f. 
- move => i j k  lij ljk; rewrite !LgV//.
    exact: (is_compose_f (iorder_gle1  lij)(iorder_gle1 ljk)).
  have w:=(iorder_preorder (proj1 H) (is_preorder_r S)).
  exact:(proj33 w _ _ _ lij ljk).
- move => i iJ;rewrite !LgV//.
    by move:(proj1 H _ iJ); rewrite is_substrate_r => /is_identity_f.
  apply: (proj32(iorder_preorder (proj1 H) (is_preorder_r S))).
  by rewrite (ipreorder_sr(is_preorder_r S)  (proj1 H)).
Defined.  

Lemma inl_restr_prop S J (H:sub_right_directed J(isr S)) :
  inductive_system_on  (inl_restr H)
      (restr (isE S) J) J (induced_order (isr S) J)
      (restr (isf S) (induced_order (isr S) J)).
Proof. by []. Qed.


Lemma inl_restr_cf_compat  S J (H:sub_right_directed J(isr S)):
  inl_map_compat (inl_restr H) (Lg J (inl_can_fun S)) (inductive_limit S).
Proof.
split; aww;  simpl.
 move => i iJ; rewrite !LgV//; apply:inl_can_fun_fp. rewrite - is_substrate_r.
 exact: (proj1 H _ iJ).
move=> i j lij; move /iorder_gleP: (lij)=> [iJ jJ leij].
by rewrite ! LgV // - (proj2 (inl_can_fun_prop leij)).
Qed.

Definition inl_restr_cf  S J (H:sub_right_directed J(isr S)):=
  (inductive_map (inl_restr H) (Lg J (inl_can_fun S)) (inductive_limit S)).

Lemma inl_restr_cf_compat2 S J (H:sub_right_directed J(isr S)):
  function_prop (inl_restr_cf H)
     (inductive_limit (inl_restr H)) (inductive_limit S).
Proof.
exact: (proj1 (inl_map_prop (inl_restr_cf_compat H))).
Qed.

Lemma inl_restr_cf_ev S J (H:sub_right_directed J (isr S)) i x:
      inc i J ->  inc x (Vg (isE S) i) ->
      Vf (inl_restr_cf H) (class (inl_equiv (inl_restr H)) (Pair.J x i)) = 
        class (inl_equiv S) (Pair.J x i).
Proof.
move => iI xE.
have xE': inc x (Vg (isE (inl_restr H)) i) by rewrite /= LgV.
rewrite (inl_inductive_map_ev (inl_restr_cf_compat H) iI xE').
by rewrite LgV // inl_can_fun_ev //; move: (proj1 H _ iI); rewrite is_substrate_r.
Qed.


Lemma sub_right_directed_trans J J' r:
  preorder r ->
   sub_right_directed J r ->
   sub_right_directed J' (induced_order r J) ->
   sub_right_directed J' r.
Proof.
move => or [ha hb][hc hd];
rewrite (ipreorder_sr or ha) in hc.
    split => //.
  by  apply: (sub_trans hc ha).
move => i j iI jI.
by move:(hd i j iI jI) => [z [za /iorder_gle1 zb /iorder_gle1 zc]]; exists z.
Qed.
  
Lemma inl_restr_canonical_comp S J J'
      (H: sub_right_directed J (isr S))
      (S' := inl_restr H)
      (H': sub_right_directed J' (isr S'))
      (g1 := inl_restr_cf H)(g2 := inl_restr_cf H')
      (g3 := inl_restr_cf (sub_right_directed_trans (is_preorder_r S) H H')):
   g1 \coP g2 /\ g3 = g1 \co g2.
Proof.
move: (inl_restr_cf_compat2 H) => [fg1 sg1 tg1].
move: (inl_restr_cf_compat2 H') => [fg2 sg2 tg2].
have res1:  g1 \coP g2 by split => //; rewrite sg1 tg2.
have res: function (g1 \co g2) by fct_tac.
split => //.
rewrite /g3; set H'':=sub_right_directed_trans _ _ _.
move: (inl_restr_cf_compat2 H'') => [fg3 sg3 tg3].
have jj: sub J' J by move: (proj1 H');  rewrite is_substrate_r.
have rr: sub (induced_order (isr S) J') (induced_order (isr S) J).
  by move => t /setI2_P [qa qb]; apply/setI2_P;split => //; apply:(setX_Sll jj).
have same_data:inl_same_data (inl_restr H'') (inl_restr H').
  by rewrite /inl_same_data /= (iorder_trans _ jj) ! double_restr.
have sg3sg2:source (inl_restr_cf H'') = source g2.
  by rewrite sg3 sg2; apply: inductive_limit_Iv.
have se:(inl_equiv (inl_restr H'')) = (inl_equiv (inl_restr H')).
  by apply: inl_equiv_Iv. 
apply: function_exten => //;aw;trivial; try ue.
rewrite sg3sg2 => t ti; rewrite compfV //.
move: ti; rewrite sg2 => /inductive_limit_hi [Qj' PE ->].
simpl in Qj', PE.
have Qj: inc (Q (rep t)) J by apply:jj.
move: PE; rewrite ! LgV// => PE.
have PE': inc (P (rep t)) (Vg (isE S') (Q (rep t))) by  rewrite /= LgV.
rewrite (inl_restr_cf_ev _ Qj' PE') (inl_restr_cf_ev _ Qj PE).
by rewrite - se inl_restr_cf_ev.
Qed.


Lemma cofinal_directed S J:
  cofinal (isr S) J -> sub_right_directed J (isr S).
Proof.
move => [pa pb]; split => // i j iI jI.
rewrite is_substrate_r in pa.
move: (is_directed_r (pa _ iI) (pa _ jI)) => [z [zI za zb]].
move:(pb _ (arg2_sr za)) => [t tI tm].
by exists t; split => //; apply:(proj33 (is_preorder_r S)) tm.
Qed.


Lemma inl_restr_cofinal S J (H:cofinal (isr S) J):
  bijection (inl_restr_cf (cofinal_directed H)).
Proof.
set H':= (cofinal_directed H).
move:(H) => []; rewrite is_substrate_r => ha hb.
have mc:=(inl_restr_cf_compat H').
split.
   apply/(inl_map_injective mc) => i x y /= iJ; rewrite ! LgV// => xE yE. 
   have iI := (ha _ iJ). 
   rewrite (inl_can_fun_ev iI xE) (inl_can_fun_ev iI yE). 
   move/(inl_class_eq_bis iI iI xE yE) => [k []]; aw => lik _ sv.
   move: (hb _ (proj2 (inl_prop0 lik))) => [j jI lkj].
   move: (f_equal (Vf (Vg (isf S) (Pair.J k j))) sv).
   rewrite(inl_prop3 lik lkj xE) (inl_prop3 lik lkj yE) => sv'.
   have lij':gle (induced_order (isr S) J) i j.
     apply/iorder_gleP; split => //.
     apply: (proj33 (is_preorder_r S) _ _ _ lik lkj).
   by exists j => //; rewrite !LgV.
move: (inl_restr_cf_compat2 H') => [ff sf tf].
split => //; rewrite sf tf.
move => y /inductive_limit_hi [Qi PE ->].
move:(hb _ Qi) => [j jI lij].
rewrite -(inl_class_of_fij lij PE); set x := Vf _ _.
have xE: inc x (Vg (isE S) j).
   move:(inl_prop4 lij) => [fui sui tui]; rewrite/x; Wtac.
exists (class (inl_equiv (inl_restr H')) (Pair.J x j)).
   by apply:inl_class_in_lim => //=; rewrite LgV.
by rewrite inl_restr_cf_ev.
Qed.

Section DoubleInductiveLimit.

Variables I1 I2 r1 r2: Set.
Hypothesis (or1: preorder r1)(or2: preorder r2)
           (sr1: substrate r1 = I1)(sr2: substrate r2 = I2)
           (dr1: right_directed_on r1 I1) (dr2: right_directed_on r2 I2).

Variable S : inductive_system.
Hypothesis Sr: isr S = prod_of_relation r1 r2.  

Lemma inl_dl_I: isI S = I1 \times I2.
Proof.
by  rewrite - is_substrate_r Sr (order_product2_sr1 or1 or2) sr1 sr2.
Qed.


Definition inl_dl_Elam_fam lam := Lg I1 (fun i => Vg (isE S) (J i lam)).
Definition inl_dl_glam_fam lam :=
  Lg r1 (fun ij => Vg (isf S) (J (J (P ij) lam) (J (Q ij) lam))).

Lemma inl_dl_index_p1 lam i: inc lam I2 -> inc i r1 ->
   gle (isr S) (J (P i) lam) (J (Q i) lam). 
Proof.
move => ha hb; rewrite Sr; apply/pidl_gleP1; split.
  by rewrite/gle /related (proj31 or1 _ hb).
by apply:(proj32 or2 lam); rewrite sr2.
Qed.


Lemma inl_dl_index_p2 lam mu i:  gle r2 lam mu -> inc i I1 ->
   gle (isr S) (J i lam) (J i mu).
Proof.
move => ha hb;  rewrite Sr;  apply/pidl_gleP1; split => //.
by apply: (proj32 or1); rewrite sr1.
Qed.                                                            


Definition inl_dl_S_lambda lam (Hl: inc lam I2) : inductive_system.
Proof.
apply(@InductiveSystem (inl_dl_Elam_fam lam) I1 r1 (inl_dl_glam_fam lam)).
- done.
- done.
- done.
- rewrite /inl_dl_Elam_fam; fprops.
- by rewrite /inl_dl_Elam_fam; aw.
- rewrite /inl_dl_glam_fam; fprops.
- by rewrite /inl_dl_glam_fam; aw.
  move => i iI.
  move:(pr1_sr iI)(pr2_sr iI); rewrite sr1 => piI qiI.
  rewrite /inl_dl_glam_fam /inl_dl_Elam_fam ! LgV//.
  by move:(is_function_f (inl_dl_index_p1 Hl iI)); aw.
- move => i j k lij ljk.
  have lik: gle r1 i k by exact: (proj33 or1 _ _ _ lij ljk).
  move:(inl_dl_index_p1 Hl lij) (inl_dl_index_p1 Hl ljk).
  rewrite/inl_dl_glam_fam !LgV //; aw; apply:(is_compose_f). 
- move => i iI.
  have pp: inc (J i lam) (isI S) by rewrite inl_dl_I; apply:setXp_i.
  have iir: inc (J i i) r1 by apply: (proj32 or1 i); rewrite sr1.
  move:(is_identity_f pp).
  by rewrite /inl_dl_glam_fam /inl_dl_Elam_fam !LgV//; aw.
Defined.

Lemma inl_dl_S_lambda_prop lam (Hl: inc lam I2) :
  inductive_system_on (inl_dl_S_lambda Hl)
     (inl_dl_Elam_fam lam) I1 r1 (inl_dl_glam_fam lam).
Proof. by []. Qed.

Definition inl_dl_system_S_lambda lam :=
  match (ixm (inc lam I2)) with
    | inl hx => (inl_dl_S_lambda hx)
    | inr _ => S
    end.

Definition inl_dl_F_lambda lam :=
  inductive_limit (inl_dl_system_S_lambda lam).

Lemma inl_dl_F_lambda_prop lam (Hl: inc lam I2): 
  inl_dl_F_lambda lam = inductive_limit (inl_dl_S_lambda Hl).
Proof.
rewrite /inl_dl_F_lambda /inl_dl_system_S_lambda.
by case: (ixm (inc lam I2)).
Qed.

Definition inl_dl_halm_fam lam mu:=
  Lg I1 (fun i => Vg (isf S) (J (J i lam) (J i mu))).


Definition inl_dl_hlm lam mu (H: gle r2 lam mu) :=
  inductive_limit_fun (inl_dl_S_lambda (pidl_i1_L sr2 H))
                      (inl_dl_S_lambda (pidl_i2_L sr2 H))
                      (inl_dl_halm_fam lam mu). 


Lemma inl_dl_halm_compat lam mu (H: gle r2 lam mu):
  inl_map2_compat (inl_dl_S_lambda (pidl_i1_L sr2 H))
                  (inl_dl_S_lambda (pidl_i2_L sr2 H))
                  (inl_dl_halm_fam lam mu).
Proof.
rewrite /inl_dl_halm_fam;split.
- fprops.
- by aw.
- move => i /= iI; rewrite /inl_dl_Elam_fam ! LgV//.
  by move:(is_function_f(inl_dl_index_p2 H iI)); aw.
- move => i j /= leij.
  move:(arg1_sr leij)(arg2_sr leij); rewrite sr1 => iI jI.
  rewrite /inl_dl_glam_fam !LgV //.
  move:(inl_dl_index_p2 H iI)(inl_dl_index_p2 H jI) => lea led.
  move: (inl_dl_index_p1  (pidl_i2_L sr2 H) leij); aw => leb.
  move: (inl_dl_index_p1  (pidl_i1_L sr2 H) leij); aw => lec.
  by rewrite (is_compose_f lea leb) (is_compose_f lec led).
Qed.


Lemma inl_dl_hlm_compose l m n
  (Hlm : gle r2 l m) (Hmn: gle r2 m n):
  (inl_dl_hlm Hmn) \co (inl_dl_hlm Hlm)  =
  (inl_dl_hlm (proj33 or2 _ _ _ Hlm Hmn)).
Proof.
move:(inl_dl_halm_compat Hlm) (inl_dl_halm_compat Hmn).
set S1 := (inl_dl_S_lambda (pidl_i1_L sr2 Hlm)).
set S2 := (inl_dl_S_lambda (pidl_i2_L sr2 Hlm)).
set S3 := (inl_dl_S_lambda (pidl_i1_L sr2 Hmn)).
set S4 := (inl_dl_S_lambda (pidl_i2_L sr2 Hmn)).
move => h1 h2.
have dS2S3: inl_same_data S2 S3 by [].
have h1': inl_map2_compat S1 S3 (inl_dl_halm_fam l m) by apply: h1.
have sd1: inl_same_index S2 S4 by [].
have sd2: inl_same_index S1 S2 by [].
rewrite -(proj2(inl_map2_compose sd2 sd1 h1' h2)).
rewrite /inl_dl_hlm.
set u := Lg _ _.
have -> //: u = (inl_dl_halm_fam l n).
rewrite /inl_dl_halm_fam /u; apply: Lg_exten => // i iI.
by rewrite /inl_dl_halm_fam !LgV//; apply: is_compose_f; apply:inl_dl_index_p2.
Qed.


Definition inl_dl_hlm_gen x :=
  match (ixm (inc x r2)) with
    | inl hx => (inl_dl_hlm (pidl_i3_L or2 hx))
    | inr _ => emptyset
    end.


Lemma inl_dl_hlm_fct lm: inc lm r2 ->
   function_prop (inl_dl_hlm_gen lm)
         (inl_dl_F_lambda (P lm))(inl_dl_F_lambda (Q lm)).
Proof.
move => lemn.
move: (pidl_i3_L or2 lemn) => H.
have ss: inl_same_index (inl_dl_S_lambda (pidl_i1_L sr2 H))
                 (inl_dl_S_lambda (pidl_i2_L sr2 H)).
   by []. 
move:(proj1 (inl_map2_prop ss (inl_dl_halm_compat H))).
move:(pidl_i1_L sr2 H)(pidl_i2_L sr2 H) => p1I p2I.
rewrite (inl_dl_F_lambda_prop p1I)(inl_dl_F_lambda_prop p2I).
by rewrite /inl_dl_hlm_gen; case: (ixm (inc lm r2)).
Qed.

Lemma inl_dl_S_lambda_Iv2 x y  (H1: inc x I2) (H2: inc y I2) : x = y ->
  inl_same_data (inl_dl_S_lambda H1)(inl_dl_S_lambda H2).
Proof. 
move => exy.
move:(inl_dl_S_lambda_prop H1) (inl_dl_S_lambda_prop H2).
rewrite /inl_same_data.
by move => [ -> _ -> ->] [ -> _ -> ->]; rewrite exy.
Qed.

Lemma  inl_dl_hml_invariant i j (H:gle r2 i j) :
   inl_dl_hlm H = inl_dl_hlm_gen (J i j).
Proof.
rewrite /inl_dl_hlm_gen.
case: (ixm (inc (J i j) r2)) => // h.
apply:inl_inductive_limit_fun_IV2.
- by apply:inl_dl_S_lambda_Iv2; aw.
- by apply:inl_dl_S_lambda_Iv2; aw.
- by aw.
Qed.

Lemma inl_dl_hml_id i: inc i I2 ->
   Vg (Lg r2 inl_dl_hlm_gen) (J i i) = identity (inl_dl_F_lambda i).
Proof.
move => i2.
have iir: inc (J i i) r2 by apply: (proj32 or2 i); rewrite sr2.
rewrite LgV // inl_dl_F_lambda_prop. 
set S1 :=  (inl_dl_S_lambda (pidl_i1_L sr2 iir)).
set S2 :=  (inl_dl_S_lambda (pidl_i2_L sr2 iir)).
have ha: (inl_same_index S1 S2) by [].
have hb:=(inl_dl_halm_compat iir).
move:(inl_map2_prop ha hb).
set f := inductive_limit_fun _ _ _.
have <-: f = inl_dl_hlm_gen (J i i) by apply:(inl_dl_hml_invariant iir).
move => [[ff sf tf] fp].
apply:function_exten.
- done.
- fprops.
- by aw.
- by aw.
- rewrite sf => x xl; rewrite idV //.
  move/(inductive_limit_hi): xl => [pa pb ->].
  have qa: inc (J (Q (rep x)) i) (isI S).
     rewrite inl_dl_I ; apply/setXp_i => //.
 have qb: inc (P (rep x)) (Vg (isE S) (J (Q (rep x)) i)).
    move: pb; simpl. rewrite/inl_dl_Elam_fam LgV//.
 by rewrite /f inl_map_val_aux2 // /inl_dl_halm_fam LgV//; rewrite inl_prop5.
Qed.

Definition inl_dl_systemS': inductive_system.
Proof.
apply(@InductiveSystem (Lg I2 inl_dl_F_lambda) I2 r2 (Lg r2 inl_dl_hlm_gen)).
- done.
- done.
- done.
- fprops.
- by aw.
- fprops.
- by aw.
- move => i i2; move: (pr1_sr i2)(pr2_sr i2); rewrite sr2 => iI jI.
  rewrite !LgV//; apply:(inl_dl_hlm_fct i2).
- move => i j k lij ljk.
  move:(proj33 or2 _ _ _ lij ljk) => lkj; rewrite !LgV//.
  move:(inl_dl_hlm_compose lij ljk).
  by rewrite 3!(inl_dl_hml_invariant).
- move => i i2; rewrite (inl_dl_hml_id i2) LgV//.
Defined.

Lemma  inl_dl_systemS'_prop: inductive_system_on inl_dl_systemS'
     (Lg I2 inl_dl_F_lambda) I2 r2 (Lg r2 inl_dl_hlm_gen).
Proof. by []. Qed.


Definition inl_dl_fg i l :=
   (inl_can_fun (inl_dl_system_S_lambda l) i).

Lemma inl_dl_fg_prop1 i l (H:inc l  I2):
  inl_dl_fg i l =  (inl_can_fun (inl_dl_S_lambda H) i).
Proof.
by rewrite /inl_dl_fg/inl_dl_system_S_lambda; case: (ixm (inc l I2)).
Qed.

Lemma inl_dl_fg_fp i l  (Hi: inc i I1) (Hl: inc l I2):
  function_prop (inl_dl_fg i l)
     (Vg (isE S) (J i l)) (inductive_limit (inl_dl_S_lambda Hl)).
Proof.
move:(inl_can_fun_fp (Hi:inc i (isI (inl_dl_S_lambda Hl)))).
rewrite inl_dl_fg_prop1 /=/inl_dl_Elam_fam LgV//. 
Qed.

Lemma inl_dl_fh_cp p 
      (h := inl_can_fun inl_dl_systemS' (Q p)) (g:= inl_dl_fg (P p) (Q p)):
  inc p (isI S) ->
  h \coP g /\ 
  function_prop (h \co g) (Vg (isE S) p) (inductive_limit (inl_dl_systemS')).
Proof.
rewrite inl_dl_I => /setX_P [pp Hi Hl].
move: (inl_dl_fg_fp Hi Hl) =>  [fg sg tg].
move: (inl_can_fun_fp (Hl:inc (Q p) (isI inl_dl_systemS'))) => [fh sh th].
have hh: source h = target g.
  by rewrite sh tg /= ! LgV//; apply: inl_dl_F_lambda_prop.
rewrite pp in sg.
split; saw; fct_tac.
Qed.

Definition inl_dl_fu :=
  Lg (isI S)  (fun  p => (inl_can_fun inl_dl_systemS' (Q p))
                           \co (inl_dl_fg (P p) (Q p))).

Lemma inl_dl_fu_compat:
  inl_map_compat S inl_dl_fu  (inductive_limit (inl_dl_systemS')).
Proof.
rewrite /inl_dl_fu; split; aww.
  move => i iI; rewrite LgV//; apply: (proj2 (inl_dl_fh_cp iI)).
move => p1 p2 lep1p2.
move:(inl_prop0 lep1p2) => [p1ii p2ii]; rewrite !LgV//.
move: (lep1p2); rewrite Sr; move/pidl_gleP => [_ _ lea leb].
move: (p1ii) (p2ii); rewrite inl_dl_I.
move => /setX_P [pp1 aI lL] /setX_P [pp2 bI mL].
have Fgbmv:= (inl_dl_fg_prop1 (P p2) mL).
set Fhm := inl_can_fun inl_dl_systemS' (Q p2).
set Fgbm := inl_dl_fg (P p2) (Q p2).
set Ffbaml := Vg (isf S) (J p1 p2).
set Fhl := inl_can_fun inl_dl_systemS' (Q p1).
set Fgal := inl_dl_fg (P p1) (Q p1).
have mI': inc (Q p2) (isI inl_dl_systemS') by [].
move: (inl_can_fun_fp mI'); rewrite -/Fhm; move => [fhm shm thm].
move: (inl_dl_fg_fp bI mL); rewrite -/Fgbm; move => [fgbm sgbm tgbm].
move: (inl_dl_fg_fp aI lL); rewrite -/Fgal; move => [fgal sgal tgal].
move: (is_function_f lep1p2).
  rewrite -/Ffbaml; aw; move => [ffbaml sfbaml tfbaml].
have co1: Fhm \coP Fgbm.
  by split => //; rewrite shm tgbm /= (LgV mL) (inl_dl_F_lambda_prop mL).
have co2:Fgbm \coP Ffbaml by split => //; rewrite sgbm pp2 tfbaml.
rewrite -(compfA co1 co2).
have lec: gle (isr S) (J (P p1) (Q p2)) p2.
  rewrite -{2} pp2 Sr; apply/pidl_gleP1; split => //.
  by apply: (proj32 or2); rewrite sr2.
have led: gle (isr S) p1 (J (P p1) (Q p2)).
  rewrite -{1} pp1 Sr; apply/pidl_gleP1; split => //.
  by apply: (proj32 or1); rewrite sr1.
move:(is_compose_f led lec); rewrite -/Ffbaml.
set Ffbamm  := Vg (isf S) (J (J (P p1) (Q p2)) p2). 
set Ffaalm  := Vg (isf S) (J p1 (J (P p1) (Q p2))).
move: (is_function_f lec) (is_function_f led);aw.
rewrite -/Ffbamm -/Ffaalm; move => [ffbamm sfbamm tfbamm][ffaalm sfaalm tfaalm].
have co3: Fgbm \coP Ffbamm by split => //; rewrite sgbm tfbamm pp2.
have co4: Ffbamm \coP Ffaalm by split => //; ue.
move <-; rewrite (compfA co3 co4).
have lee: gle (isr (inl_dl_S_lambda mL)) (P p1) (P p2)  by [].
move: (proj2 (inl_can_fun_prop lee)).
rewrite - Fgbmv /= /inl_dl_glam_fam LgV//; aw; rewrite pp2  -/Ffbamm => <-.
have eqx: Ffaalm = Vg (inl_dl_halm_fam (Q p1) (Q p2)) (P p1).
  by rewrite /inl_dl_halm_fam LgV//; rewrite pp1.
set S1 := (inl_dl_S_lambda (pidl_i1_L sr2 leb)).
set S2 := (inl_dl_S_lambda (pidl_i2_L sr2 leb)).
have aI': inc (P p1) (isI  S1) by [].
have ssi: inl_same_index  S1 S2 by [].
move:(inl_map2_prop ssi (inl_dl_halm_compat leb)).
set Fgam := inductive_limit_fun _ _ _.
move=> [[fgam sgam tgam] vgam].
move:(vgam _ aI'); rewrite {1} /inl_dl_halm_fam LgV// pp1; move ->.
rewrite - inl_dl_fg_prop1 -/Fgal.
have co5: Fhm \coP Fgam.
  by split => //; rewrite shm tgam /= LgV//; apply: inl_dl_F_lambda_prop.
have co6: Fgam \coP Fgal by split => //; ue.
rewrite (compfA co5 co6); congr compose.
have : gle (isr inl_dl_systemS') (Q p1) (Q p2) by [].
by move/inl_can_fun_prop => /proj2 /=; rewrite LgV// - inl_dl_hml_invariant. 
Qed.

Lemma inl_dl_bijection: bijection_prop
     (inductive_map S inl_dl_fu (inductive_limit inl_dl_systemS'))
     (inductive_limit S) (inductive_limit inl_dl_systemS').
Proof.
have H := inl_dl_fu_compat.
move:(proj1 (inl_map_prop H)).
set mfun := inductive_map _ _ _; move => [ff sf tf].
have imf:injection mfun.
  apply /(inl_map_injective H) => p x y ps xE yE.
  move:(ps); rewrite inl_dl_I => /setX_P [pp iI lL].
  move:(proj1 (inl_dl_fh_cp ps)) => ha.
  move:(inl_dl_fg_prop1 (P p) lL); set fa := inl_can_fun _ _ => eq1.
  have iI': inc (P p) (isI (inl_dl_S_lambda lL)) by [].
  case:(inl_can_fun_fp  iI'); rewrite -/fa => ffa sfa tfa.
  have sfa':source fa = Vg (isE S) p. 
    by move: sfa; rewrite /= /inl_dl_Elam_fam LgV// pp.
  have xs: inc x (source (inl_dl_fg (P p) (Q p))) by rewrite eq1 sfa'.
  have ys: inc y (source (inl_dl_fg (P p) (Q p))) by rewrite eq1 sfa'.
  have xs':inc x (Vg (isE (inl_dl_S_lambda lL)) (P p)) by rewrite - sfa sfa'.
  have ys':inc y (Vg (isE (inl_dl_S_lambda lL)) (P p)) by rewrite - sfa sfa'.
  rewrite /inl_dl_fu; rewrite LgV// ! compfV //  eq1 /fa.
  have lL':inc (Q p) (isI inl_dl_systemS') by [].
  rewrite (inl_can_fun_ev iI' xs') (inl_can_fun_ev iI' ys').
  have eq2: (Vg (isE inl_dl_systemS') (Q p)) =
            inductive_limit (inl_dl_S_lambda lL). 
    by rewrite /= LgV //inl_dl_F_lambda_prop.
  have fxs: inc (class (inl_equiv (inl_dl_S_lambda lL)) (J x (P p)))
     (Vg (isE inl_dl_systemS') (Q p)).
     by rewrite eq2; apply: inl_class_in_lim.
  have fys: inc (class (inl_equiv (inl_dl_S_lambda lL)) (J y (P p)))
     (Vg (isE inl_dl_systemS') (Q p)).
     by rewrite eq2; apply: inl_class_in_lim.
  rewrite (inl_can_fun_ev lL' fxs) (inl_can_fun_ev lL' fys).
  move/(inl_class_eq_bis lL' lL' fxs fys) => [i]; aw.
  move => [ai _]; rewrite /= LgV//- inl_dl_hml_invariant.
  have cc:= (inl_dl_halm_compat ai).
  have cc':inl_same_index (inl_dl_S_lambda (pidl_i1_L sr2 ai))
   (inl_dl_S_lambda (pidl_i2_L sr2 ai)) by [].
  rewrite (inl_map_val_aux2 cc' cc iI xs') (inl_map_val_aux2 cc' cc iI ys').
  rewrite /inl_dl_halm_fam LgV //.
  move/(inl_class_eq_bis); simpl; rewrite pp /inl_dl_Elam_fam LgV// => Hx.
  have lea: gle (isr S) p (J (P p) i).
    rewrite - {1} pp Sr; apply/pidl_gleP1; split => //.
    by apply: (proj32 or1); rewrite sr1.
  move :(inl_prop4 lea) => [fb sb tb].
  have xs2:inc (Vf (Vg (isf S) (J p (J (P p) i))) x) (Vg (isE S) (J (P p) i)).
     Wtac.
  have ys2:inc (Vf (Vg (isf S) (J p (J (P p) i))) y) (Vg (isE S) (J (P p) i)).
     Wtac.
  move: (Hx iI iI xs2 ys2) => [j []]; simpl; aw => leb _.
  have lec: gle (isr S) (J (P p) i) (J j i).
    rewrite Sr; apply/pidl_gleP1; split => //.
    apply: (proj32 or2); exact: (arg2_sr ai). 
  rewrite /inl_dl_glam_fam LgV//; aw.
  rewrite inl_prop3 // inl_prop3 // => h.
  by exists (J j i) => //; rewrite - pp Sr; apply/pidl_gleP1.
split => //; split => //.
split => //; rewrite sf tf  => y /inductive_limit_hi /= [].
set l := (Q (rep y)) => lL.
rewrite LgV // inl_dl_F_lambda_prop.
move => /inductive_limit_hi /= []; set i:= (Q (rep (P (rep y)))) => iI.
have ilI: inc (J i l) (isI S) by  rewrite inl_dl_I; apply: setXp_i.
move:(proj1 (inl_dl_fh_cp ilI)); aw => co1.
set x:= P _; rewrite /inl_dl_Elam_fam LgV//; move => xE -> ->.
exists (class (inl_equiv S) (J x (J i l))).
   apply: (inl_class_in_lim ilI xE).
rewrite /mfun; rewrite (inl_inductive_map_ev inl_dl_fu_compat ilI xE).
rewrite /inl_dl_fu (LgV ilI) pr1_pair pr2_pair.
have iI':inc i (isI (inl_dl_S_lambda lL) ) by [].
have xEb: (Vg (isE (inl_dl_S_lambda lL)) i) = Vg (isE S) (J i l).
  rewrite /= /inl_dl_Elam_fam LgV//.
have xE':  inc x (Vg (isE (inl_dl_S_lambda lL)) i) by rewrite xEb.
move:(inl_can_fun_fp iI') => [fcf scf tcf].
have xE'':inc x (source (inl_can_fun (inl_dl_S_lambda lL) i)) by ue.
move: co1; rewrite inl_dl_fg_prop1 => co1; rewrite compfV//.
have ww: inc (Vf (inl_can_fun (inl_dl_S_lambda lL) i) x)
     (Vg (isE inl_dl_systemS') l).
   move: tcf;simpl;rewrite LgV // inl_dl_F_lambda_prop => <-; Wtac.
have eq1:= (inl_can_fun_ev iI' xE').
by rewrite eq1 inl_can_fun_ev // - eq1. 
Qed.  

End DoubleInductiveLimit.


Section  DoubleDirectLimit2.

Variables I1 I2 r1 r2: Set.
Hypothesis (or1: preorder r1)(or2: preorder r2)
           (sr1: substrate r1 = I1)(sr2: substrate r2 = I2).
Hypothesis (dr1: right_directed_on r1 I1) (dr2: right_directed_on r2 I2).

Variables S S': inductive_system.
Variable u: Set.
Hypothesis Sr: isr S = prod_of_relation r1 r2.
Hypothesis Sr': isr S' = prod_of_relation r1 r2.
Hypothesis compat_u: inl_map2_compat S S' u.

Lemma inl_dl2_SrSr: inl_same_index S S'. 
Proof. by rewrite/inl_same_index Sr Sr'. Qed.
  
Definition inl_dl2_ulam_fam lam :=  Lg I1 (fun i => Vg u (J i lam)).
Definition inl_dl2_Slambda := (inl_dl_system_S_lambda or1 or2 sr1 sr2 dr1 Sr).
Definition inl_dl2_Slambda' := (inl_dl_system_S_lambda or1 or2 sr1 sr2 dr1 Sr').

Lemma inl_dl2_res1 lam:inc lam I2 ->
   inl_same_index (inl_dl2_Slambda lam) (inl_dl2_Slambda' lam) /\
   inl_map2_compat (inl_dl2_Slambda lam) (inl_dl2_Slambda' lam)
                  (inl_dl2_ulam_fam lam).
Proof.
move => li2.
rewrite /inl_same_index/inl_map2_compat.
set S1 := (inl_dl_S_lambda  or1 or2 sr1 sr2 dr1 Sr li2).
set S2 := (inl_dl_S_lambda  or1 or2 sr1 sr2 dr1 Sr' li2).
have [ES1 rS1 fS1]: inl_same_data (inl_dl2_Slambda lam) S1.
    rewrite/inl_dl2_Slambda/inl_dl_system_S_lambda.
    by case: (ixm (inc lam I2)).
have [ES2 rS2 fS2]: inl_same_data (inl_dl2_Slambda' lam) S2.
    rewrite/inl_dl2_Slambda'/inl_dl_system_S_lambda.
    by case: (ixm (inc lam I2)).
rewrite/inl_same_index rS1 rS2.
split; first exact.
have ->: isI (inl_dl2_Slambda lam) = I1.
  by rewrite - is_domain_E ES1 /= /inl_dl_Elam_fam; aw.
rewrite /inl_dl2_ulam_fam ES1 ES2; split.
+ fprops.
+ by aw.
+ move => i iI1; rewrite ! LgV // /= /inl_dl_Elam_fam; aw.
  have ilI: inc (J i lam) (isI S).
    by rewrite -is_substrate_r Sr (proj2(pidl_or or1 or2 sr1 sr2)); fprops.
  exact:(proj43 compat_u _ ilI).
+ move => i j lij; rewrite fS1 fS2.
  move:(inl_prop0 lij) => [iI jI].
  rewrite /= /inl_dl_glam_fam ! LgV//; aw.
  apply:(proj44 compat_u  (J i lam)  (J j lam)). 
  rewrite Sr; apply/pidl_gleP; split;aww.
  apply:(proj32 or2); ue.
Qed.

Definition inl_dl2_v lam :=
   inductive_limit_fun (inl_dl2_Slambda lam) (inl_dl2_Slambda' lam)
                  (inl_dl2_ulam_fam lam).
Definition inl_dl2_v_fam := Lg I2 inl_dl2_v. 


Definition inl_dl2_limlim := (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr).
Definition inl_dl2_limlim' := (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr').

Lemma inl_dl2_res2:
  inl_map2_compat inl_dl2_limlim  inl_dl2_limlim' inl_dl2_v_fam.
Proof.
rewrite /inl_dl2_v_fam; split.
- fprops.
- by aw.
- move => i /= iI2; rewrite !LgV//.
  move:(inl_dl2_res1 iI2) => [ha hb].
  exact: (proj1 (inl_map2_prop ha hb)).
- move => i j /= leij'.
move:(arg1_sr leij')(arg2_sr leij'); rewrite sr2 => iI2 jI2.
rewrite !LgV ///inl_dl_hlm_gen; case: (ixm (inc (J i j) r2)) => // leij.
clear leij'.
set V := inl_dl2_v.
set hlm := inl_dl_hlm or1 or2 sr1 sr2 dr1 Sr (pidl_i3_L or2 leij).
set hlm' := inl_dl_hlm or1 or2 sr1 sr2 dr1 Sr' (pidl_i3_L or2 leij).
move:(inl_dl2_res1 iI2)(inl_dl2_res1 jI2) =>[ha hb][ha' hb'].
move: (inl_map2_prop3 ha hb) (inl_map2_prop3 ha' hb').
rewrite -/(inl_dl2_v _) -/(inl_dl2_v _) -/V.
set Si := inductive_limit _; set Si' := inductive_limit _.
set Sj := inductive_limit _; set Sj' := inductive_limit _.
move => [[fvi svi tvi]  Vip] [[fvj svj tvj] Vjp].

set T := inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr. 
set T' := inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr'.
have sid1:inl_same_index (T  _ (pidl_i1_L sr2 leij))
     (T  _ (pidl_i2_L sr2 leij)) by [].
set QQ := inl_dl_halm_compat or1 or2 sr1 sr2 dr1.
move: (inl_map2_prop3 sid1 (QQ _  Sr _ _ leij)).
simpl;  rewrite -/(inl_dl_hlm _ _ _ _ _ _ _) inl_dl_hml_invariant.  
have ->: (inl_dl_hlm_gen or1 or2 sr1 sr2 dr1 Sr (J i j)) = hlm. 
  by rewrite /hlm inl_dl_hml_invariant; aw.
rewrite -inl_dl_F_lambda_prop  -inl_dl_F_lambda_prop.
rewrite /inl_dl_F_lambda -/Si - /Sj.
move => [[fLa sLa tLa] Lap].
have sid2:inl_same_index (T' _ (pidl_i1_L sr2 leij))
     (T' _ (pidl_i2_L sr2 leij)) by [].
move:(inl_map2_prop3 sid2 (QQ _ Sr' _ _ leij)).
simpl;  rewrite  -/(inl_dl_hlm _ _ _ _ _ _ _) inl_dl_hml_invariant.
have ->: (inl_dl_hlm_gen or1 or2 sr1 sr2 dr1 Sr' (J i j)) = hlm'. 
  by rewrite /hlm' inl_dl_hml_invariant; aw.
rewrite- inl_dl_F_lambda_prop  -inl_dl_F_lambda_prop.
rewrite /inl_dl_F_lambda -/Si' - /Sj'.
move => [[fLb sLb tLb] Lbp].
have res1: V j \coP hlm by split => //; ue.
have res2: hlm' \coP V i by split => //; ue.
apply:function_exten.
+ by apply: compf_f.
+ by apply: compf_f.
+ aw; ue.
+ aw; ue.
+ aw; rewrite svi => x xsi.
  have xs1:inc x (source (V i)) by ue.
  have xs2: inc x (source hlm) by ue.
  rewrite ! compfV //.
have qe: isI (inl_dl2_Slambda i) = I1.
  rewrite /inl_dl2_Slambda /inl_dl_system_S_lambda.
  by case: (ixm (inc i I2)).
have qe': isI (inl_dl2_Slambda j) = I1.
  rewrite /inl_dl2_Slambda /inl_dl_system_S_lambda.
  by case: (ixm (inc j I2)).
move/inductive_limit_hi: xsi;set k := Q _ ; set xk := P _.
move=>  [ra rb ->]; rewrite (Vip _ _ ra rb). 
move:(ra). rewrite qe - qe' => ra'.
move: ra; rewrite qe => kI1.
have rb1: inc xk (Vg (isE S) (J k i)).
  move: rb; rewrite /inl_dl2_Slambda /inl_dl_system_S_lambda.
  case: (ixm (inc i I2)) => // HH.
  by  rewrite /= /inl_dl_Elam_fam LgV.
have rb2: inc xk (Vg (inl_dl_Elam_fam I1 S i) k).
  by rewrite /inl_dl_Elam_fam LgV.
have kiI:  inc (J k i) (isI S). 
  rewrite - is_substrate_r Sr (proj2(pidl_or or1 or2 sr1 sr2)); fprops.
move: (proj43 compat_u _ kiI) => [fuki suki tuki].
set xk1 := (Vf (Vg u (J k i)) xk).  
have ukixE: inc xk1 (Vg (inl_dl_Elam_fam I1 S' i) k).
  rewrite /xk1 /inl_dl_Elam_fam LgV//; Wtac. 
rewrite /inl_dl2_ulam_fam LgV//.
move: (Lbp k xk1 kI1 ukixE).
set c1 := class _ (J xk1 k).
set c2 := class _ (J xk1 k).
have cc : c1 = c2.
  rewrite /c1 /c2 /T' /inl_dl2_Slambda' /inl_dl_system_S_lambda.
  by case: (ixm (inc i I2)).
rewrite cc => ->; clear c1 c2 cc.
move: (Lap k xk kI1 rb2).
set c1 := class _ (J xk k).
set c2 := class _ (J xk k).
have cc : c1 = c2.
  rewrite /c1 /c2 /T /inl_dl2_Slambda /inl_dl_system_S_lambda.
  by case: (ixm (inc i I2)).
rewrite cc => ->; clear c1 c2 cc.
set xk2:= (Vf (Vg (inl_dl_halm_fam I1 S i j) k) xk).
have gle0: gle (isr S) (J k i) (J k j).
      rewrite Sr; apply/pidl_gleP1; split => //.
      by apply: (proj32 or1); rewrite sr1.
move/inl_prop4: (gle0) =>[ff sf tf].
have rb3: inc xk2 (Vg (isE (inl_dl2_Slambda j)) k).
   rewrite /inl_dl2_Slambda /inl_dl_system_S_lambda.
   case: (ixm (inc j I2)) => // H.
   rewrite /= /inl_dl_Elam_fam /xk2 /inl_dl_halm_fam ! LgV//; Wtac.
rewrite /inl_dl_halm_fam LgV//.
move: (Vjp k xk2 ra' rb3).
set c1 := class _ (J xk2 k).
set c2 := class _ (J xk2 k).
have cc : c1 = c2.
  rewrite /c1 /c2 /T /inl_dl2_Slambda /inl_dl_system_S_lambda.
  by case: (ixm (inc j I2)).
rewrite cc; move ->; clear c1 c2 cc.
rewrite /inl_dl2_ulam_fam LgV //.
congr class; last (congr J).
  rewrite /T'/inl_dl2_Slambda'/ inl_dl_system_S_lambda.
  by case: (ixm (inc j I2)).
have kjI:  inc (J k j) (isI S). 
  rewrite - is_substrate_r Sr (proj2(pidl_or or1 or2 sr1 sr2)); fprops.
move: (proj43 compat_u _ kjI) => [fukj sukj tukj].
move: (gle0); rewrite Sr - Sr' => /inl_prop4[ff' sf' tf'].
have co1: Vg u (J k j) \coP Vg (isf S) (J (J k i) (J k j)) by split => //; ue.
have co2: Vg (isf S') (J (J k i) (J k j)) \coP Vg u (J k i) by split => //; ue.
have xkE': inc xk (source (Vg (isf S) (J (J k i) (J k j)))) by ue.
have xkE: inc xk (source (Vg u (J k i))) by ue.
move:(f_equal (Vf ^~xk) (proj44 compat_u _ _ gle0)).
rewrite !compfV //; move ->; rewrite /xk2 /inl_dl_halm_fam ! LgV//.
Qed.

Lemma inl_dl2_res3
  (bij1 := (inductive_map S (inl_dl_fu or1 or2 sr1 sr2 dr1 dr2 Sr)
            (inductive_limit (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr))))
  (bij2 := (inductive_map S' (inl_dl_fu or1 or2 sr1 sr2 dr1 dr2 Sr')
            (inductive_limit (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr'))))
  (pl1 := inductive_limit_fun S S' u)
  (pl2 := inductive_limit_fun inl_dl2_limlim  inl_dl2_limlim' inl_dl2_v_fam):
  [/\ bijection bij1, bijection bij2 & pl2 \co bij1  =  bij2 \co pl1].
Proof.
move:(inl_map2_prop3 inl_dl2_SrSr compat_u) => /=.
rewrite -/pl1.
set E :=  (inductive_limit S); set E':= (inductive_limit S').
move => [[fpl1 spl1 tpl1] pl1_prop].
have ha: inl_same_index inl_dl2_limlim inl_dl2_limlim' by [].
move: (inl_map2_prop3 ha inl_dl2_res2); simpl.
rewrite -/pl2.
set vE:= inductive_limit _; set vE':= inductive_limit _.
move => [[fpl2 spl2 tpl2] pl2_prop].
move:(inl_dl_bijection or1 or2 sr1 sr2 dr1 dr2 Sr).
move:(inl_dl_bijection or1 or2 sr1 sr2 dr1 dr2 Sr').
rewrite -/bij1 -/bij2 -/E -/E' -/vE -/vE'.
move => [bp2 sf2 tf2] [bp1 sf1 tf1].
split => //.
move:(bp2)(bp1) => [[ff1 _] _] [[ff2 _] _].
have co1: pl2 \coP bij1 by split => //; ue.
have co2: bij2 \coP pl1 by split => //; ue.
apply: function_exten;try (apply: compf_f => //);  aw; try ue.
rewrite sf1 => x /inductive_limit_hi.
set il := Q _; set xb:= P _; move => [ilI hb  ->].
have xs1:  inc (class (inl_equiv S) (J xb il)) (source pl1).
  by rewrite spl1; apply: inl_class_in_lim.
move: (xs1); rewrite  spl1 - sf1 => xs2; rewrite !compfV //.
have ilI':inc il (isI S') by rewrite -(inl_same_index_same_I inl_dl2_SrSr).
rewrite (pl1_prop _ _ ilI hb).
move: (proj43 compat_u _ ilI) =>[fu su tu].
have xs4:inc (Vf (Vg u il) xb) (Vg (isE S') il) by Wtac.
move: (inl_dl_fu_compat or1 or2 sr1 sr2 dr1 dr2 Sr') => comp2.
move: (inl_dl_fu_compat or1 or2 sr1 sr2 dr1 dr2 Sr) => comp1.
rewrite /bij2  (inl_inductive_map_ev comp2 ilI' xs4).
rewrite /bij1  (inl_inductive_map_ev comp1 ilI hb).
move:(proj1 (inl_dl_fh_cp  or1 or2 sr1 sr2 dr1 dr2 Sr ilI)) => cop1.
move:(proj1 (inl_dl_fh_cp  or1 or2 sr1 sr2 dr1 dr2 Sr' ilI')) => cop2.
move:(ilI); rewrite - is_substrate_r Sr (proj2(pidl_or or1 or2 sr1 sr2)).
move => /setX_P [pil iI1 lI2].
have xs3: inc xb (source (inl_dl_fg or1 or2 sr1 sr2 dr1 Sr (P il) (Q il))).
  move:(inl_dl_fg_fp  or1 or2 sr1 sr2 dr1 Sr iI1 lI2)=> [ff sf tf].
  by rewrite sf pil.
have xs5: inc (Vf (Vg u il) xb)
   (source (inl_dl_fg or1 or2 sr1 sr2 dr1 Sr' (P il) (Q il))).
    move:(inl_dl_fg_fp  or1 or2 sr1 sr2 dr1 Sr' iI1 lI2)=> [ff sf tf].
   rewrite sf pil; Wtac.
rewrite /inl_dl_fu ! LgV// !compfV //.
rewrite inl_dl_fg_prop1 inl_dl_fg_prop1.
have ra: inc (P il)(isI (inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr lI2)) by [].
have rb: inc xb
   (Vg (isE (inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr lI2)) (P il)).
   by rewrite /= /inl_dl_Elam_fam LgV// pil.
have ra':inc (Q il) (isI (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr)) by [].
have rb': inc
   (class (inl_equiv (inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr lI2))
      (J xb (P il)))
   (Vg (isE (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr)) (Q il)).
  rewrite /= LgV//inl_dl_F_lambda_prop.
  by apply:inl_class_in_lim.
rewrite (inl_can_fun_ev ra rb) (inl_can_fun_ev ra' rb').
have ra2: inc (P il)(isI (inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr' lI2)) by [].
have ra2':inc (Q il) (isI (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr')) by [].
have rb2: inc (Vf (Vg u il) xb)
   (Vg (isE (inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr' lI2)) (P il)).
  by rewrite /= /inl_dl_Elam_fam LgV// pil.
have rb2': inc
   (class (inl_equiv (inl_dl_S_lambda or1 or2 sr1 sr2 dr1 Sr' lI2))
      (J (Vf (Vg u il) xb) (P il)))
   (Vg (isE (inl_dl_systemS' or1 or2 sr1 sr2 dr1 dr2 Sr')) (Q il)).
   rewrite /= LgV//inl_dl_F_lambda_prop.
  by apply:inl_class_in_lim.
rewrite (inl_can_fun_ev ra2 rb2) (inl_can_fun_ev ra2' rb2').
rewrite (pl2_prop _ _ lI2 rb')/ inl_dl2_v_fam LgV//.
move:(inl_dl2_res1 lI2) => [rxa rxb].
move: (inl_map2_prop3 rxa rxb) => [bof hh].
have ra3: inc (P il) (isI (inl_dl2_Slambda (Q il))).
   rewrite /inl_dl2_Slambda /inl_dl_system_S_lambda.
   by case: (ixm (inc (Q il) I2)).
have rb3: inc xb (Vg (isE (inl_dl2_Slambda (Q il))) (P il)).
    rewrite /inl_dl2_Slambda /inl_dl_system_S_lambda.
    by case: (ixm (inc (Q il) I2)).
move:(hh (P il) xb ra3 rb3); rewrite -/(inl_dl2_v (Q il)).
rewrite  /inl_dl2_Slambda  /inl_dl2_Slambda' /inl_dl_system_S_lambda.
case: (ixm (inc (Q il) I2)) => // Ha ->.
by rewrite/inl_dl2_ulam_fam LgV// pil.
Qed.

End  DoubleDirectLimit2.






Definition inl_product_E S S':= 
   Lg (isI S) (fun i => (Vg (isE S) i) \times (Vg (isE S') i)).
Definition inl_product_f S S' := 
   Lg (isr S) (fun i => (Vg (isf S) i) \ftimes (Vg (isf S') i)).

Definition inl_system_product S S' (sd: inl_same_index S S'): inductive_system.
Proof.
apply:(@InductiveSystem (inl_product_E S S') (isI S) (isr S)
                           (inl_product_f S S')).
- exact:(is_preorder_r S).
- exact (is_substrate_r S).
- exact (@is_directed_r S).
- rewrite /inl_product_E ; fprops.
- by rewrite /inl_product_E ; aw.
- rewrite /inl_product_f ; fprops.
- by rewrite /inl_product_f ; aw.
- move => i ir.
  move:(ir); rewrite sd => ir'.
  have pi:= ((proj31 (is_preorder_r S)) _ ir).
  move:(ir);rewrite -{1} pi  => /inl_prop0 [pI qI].
  rewrite /inl_product_E /inl_product_f !LgV//.
  exact: (ext_to_prod_fun_bis (is_function_f ir) (is_function_f ir')).
- move => i j k lij ljk.
  move:(proj33 (is_preorder_r S) _ _ _ lij ljk) => lik.
  move:(lij)(ljk); rewrite sd => lij' ljk'.
  rewrite /inl_product_f ! LgV//.
  move: (is_function_f lij)(is_function_f lij'); aw => ha hb.
  move: (is_function_f ljk)(is_function_f ljk'); aw => hc hd.
  rewrite (ext_to_prod_comp_bis ha hb hc hd ) !is_compose_f //.
- move => i iI.
  have iI': inc i (isI S') by rewrite - (inl_same_index_same_I sd).
  move:(inl_prop1 iI) => iiI.
  rewrite /inl_product_f /inl_product_E ! LgV//.
  rewrite !is_identity_f //; apply:ext_to_prod_identity.
Defined.


Lemma inl_system_product_prop S S' (sd: inl_same_index S S'):
  inductive_system_on (inl_system_product sd) 
   (inl_product_E S S') (isI S) (isr S) (inl_product_f S S').
Proof. by []. Qed.

Definition inl_product_can_fun S S' :=
  Lg (isI S) (fun i => (inl_can_fun S i) \ftimes (inl_can_fun S' i)).


Lemma inl_product_can_fun_compat  S S' (sd: inl_same_index S S'):
  inl_map_compat (inl_system_product sd) (inl_product_can_fun S S')
  ((inductive_limit S) \times (inductive_limit S')).
Proof.
move:(inl_system_product_prop sd) => [ha hb hc hd].
have ssI := inl_same_index_same_I sd.
rewrite /inl_product_can_fun ; split; aww.
   rewrite ha /inl_product_E; move => i iI; rewrite ! LgV//.
  by apply:ext_to_prod_fun_bis; apply:inl_can_fun_fp => //; rewrite - ssI.
rewrite hc;move => i j lij.
move: (inl_prop0 lij) => [iI jI]. rewrite LgV// LgV// hd /inl_product_f LgV//.
have jI': inc j (isI S') by rewrite - ssI.
have lij':  gle (isr S') i j by rewrite - sd.
move: (is_function_f lij) (is_function_f lij'); aw => h3 h4.
rewrite(ext_to_prod_comp_bis h3 h4 (inl_can_fun_fp jI) (inl_can_fun_fp jI')).
by rewrite - (proj2(inl_can_fun_prop lij))  (proj2(inl_can_fun_prop lij')).
Qed.
  

Lemma inl_product_can_fun_bij  S S' (sd: inl_same_index S S')
  (E:=  inductive_limit S) (E' := inductive_limit S')
  (f:= inductive_map (inl_system_product sd) (inl_product_can_fun S S')
         (E \times E')):
   bijection_prop f
       (inductive_limit (inl_system_product sd)) (E \times E').
Proof.
move:(inl_system_product_prop sd) => [pa pb pc pd].
move:(inl_product_can_fun_compat sd) => ha.
move:(inl_map_prop ha) (inl_map_ax ha).
have ssI:= (inl_same_index_same_I sd).
rewrite -/E -/E' -/f; move =>[hc hd ] he.
rewrite /f/inductive_map; saw.
split.
  apply/(inl_map_injective ha); move => i x y /= iI.
  rewrite/inl_product_E/inl_product_can_fun. rewrite !LgV//.
  move => /setX_P [px Px Qx] /setX_P [py Py Qy].
  move: (inl_can_fun_fp iI) => [fi si ti].
  move:(iI); rewrite ssI => iI'.
  move: (inl_can_fun_fp iI') => [fi' si' ti'].
  have ra: inc (P y) (source (inl_can_fun S i)) by ue.
  have rb: inc (Q y) (source (inl_can_fun S' i)) by ue.
  have rc: inc (P x) (source (inl_can_fun S i)) by ue.
  have rd: inc (Q x) (source (inl_can_fun S' i)) by ue.
  rewrite -px - py ext_to_prod_V // ext_to_prod_V //.
  do 4 rewrite inl_can_fun_ev //. 
  move => eq1; move:(pr1_def eq1) (pr2_def eq1); clear eq1.
  move/(inl_class_eq_bis iI iI Px Py) => [k []]; aw => lik _ eq2.
  move/(inl_class_eq_bis iI' iI' Qx Qy) => [k' []]; aw => lik' _ eq2'.
  move:(proj2(inl_prop0 lik)) (proj2(inl_prop0 lik')); rewrite - ssI => kI kI'.
  move: (is_directed_r kI kI') => [l [lI lkl lkl']].
  move: (proj33 (is_preorder_r S) _ _ _ lik lkl) => lil.
  move:(inl_prop4 lil) => [fil sil til].
  move:(lil); rewrite sd => lil'; rewrite sd in lkl'.
  move:(inl_prop4 lil') => [fil' sil' til'].
  have ra': inc (P y) (source (Vg (isf S) (J i l))) by ue.
  have rb': inc (Q y) (source (Vg (isf S') (J i l))) by ue.
  have rc': inc (P x) (source (Vg (isf S) (J i l))) by ue.
  have rd': inc (Q x) (source (Vg (isf S') (J i l))) by ue. 
  exists l => //=. 
  rewrite /inl_product_f LgV// ext_to_prod_V // ext_to_prod_V //.
  rewrite -(inl_prop3 lik lkl Px) - (inl_prop3 lik lkl Py) eq2.
  by rewrite -(inl_prop3 lik' lkl' Qx) - (inl_prop3 lik' lkl' Qy) eq2'.

apply:lf_surjective => // y /setX_P[py  Py Qy].
move/inductive_limit_hi:Py => [sa sb sc].
move/inductive_limit_hi:Qy => [sa' sb' sc'].
rewrite - ssI in sa'.
move:(is_directed_r sa sa') => [k [kI lik ljk]].
move: sc; rewrite -(inl_class_of_fij lik sb); set y1 := Vf _ _ => Py. 
rewrite sd in ljk.
move: sc'; rewrite-(inl_class_of_fij ljk sb'); set y2 := Vf _ _ => Qy. 
move:(inl_can_fun_fp kI) => [fk sk tk].
move:(kI); rewrite ssI =>  kI'.
move:(inl_can_fun_fp kI') => [fk' sk' tk'].
have ra: inc y2 (Vg (isE S') k).
    move:(inl_prop4 ljk) => [ff sf tf];rewrite /y2; Wtac.
have rb: inc y2 (source (inl_can_fun S' k)) by ue.
have rc : inc y1 (Vg (isE S) k).
  move:(inl_prop4 lik) => [ff sf tf];rewrite /y1; Wtac.
have rd: inc y1 (source (inl_can_fun S k)) by ue.
have pE:inc (J y1 y2) (Vg (isE (inl_system_product sd)) k).
  by rewrite /= /inl_product_E LgV//; apply: setXp_i.
set x := (class (inl_equiv (inl_system_product sd)) (J (J y1 y2) k)).
have xl: inc x (inductive_limit (inl_system_product sd)).
  by apply: (inl_class_in_lim). 
exists x => //.
move:(inl_map_property_res1 ha (inl_map_prop ha) kI pE).
rewrite /inductive_map LfV// => ->; rewrite /inl_product_can_fun LgV//.
by rewrite ext_to_prod_V // inl_can_fun_ev // inl_can_fun_ev //  - Py - Qy py.
Qed.

Section InjectiveProductMap.
Variables (SE SE' SF SF': inductive_system).
Variables u u': Set.
Hypotheses (si1:inl_same_index SE SE')
           (si2:inl_same_index SE SF)
           (si3:inl_same_index SF SF').
Hypotheses (cu:inl_map2_compat SE SF u) (cu':inl_map2_compat SE' SF' u').

Lemma inl_prod_si4: inl_same_index SE' SF'.
Proof. by rewrite /inl_same_index - si1 si2. Qed.
  
Definition inl_prod_SEE := inl_system_product si1.
Definition inl_prod_SFF := inl_system_product si3.

Definition inl_prod_uu:= Lg (isI SE) (fun i => (Vg u i) \ftimes (Vg u' i)).

Lemma inl_prod_uu_prop:inl_map2_compat inl_prod_SEE inl_prod_SFF inl_prod_uu.
Proof.
rewrite /inl_prod_uu; split; aww.
  move => i /= iI; rewrite LgV // /inl_product_E.
  have qa: inc i (isI SF) by rewrite - (inl_same_index_same_I  si2).
  have qb: inc i (isI SE') by rewrite - (inl_same_index_same_I  si1).
  move:(proj43 cu _ iI) (proj43 cu' _ qb) => fpa fpb.
  by rewrite !LgV //; apply:ext_to_prod_fun_bis.
move => i j /= leij.
move:(inl_prop0 leij) => [iI jI].
have ha: inc (J i j) (isr SF) by rewrite - si2.
have hb: inc (J i j) (isr SF') by rewrite - si3.
have hc: inc (J i j) (isr SE') by rewrite - si1.
move:(inl_prop0 hc) => [iI' jI'].
rewrite /inl_product_f !LgV //.
move:(inl_prop4 leij)(inl_prop4 hc)(inl_prop4 ha)(inl_prop4 hb) => h1 h2 h3 h4.
move:(proj43 cu _ iI) (proj43 cu _ jI) => fpui fpuj.
move:(proj43 cu' _ iI') (proj43 cu' _ jI') => fpui' fpuj'.
move:(proj44 cu _ _ leij) (proj44 cu' _ _ hc) => uv1 uv2.
rewrite (ext_to_prod_comp_bis fpui fpui' h3 h4).
by rewrite uv1 uv2 (ext_to_prod_comp_bis h1 h2 fpuj fpuj').
Qed.

Lemma inl_prod__uu_comp
  (E := inductive_limit SE)
  (E' := inductive_limit SE')
  (F := inductive_limit SF)
  (F' := inductive_limit SF')
  (EE:= inductive_limit (inl_system_product si1))
  (FF:= inductive_limit (inl_system_product si3))
  (lu:= inductive_limit_fun SE SF u)
  (lu':= inductive_limit_fun SE' SF' u')
  (luu:= inductive_limit_fun inl_prod_SEE inl_prod_SFF inl_prod_uu)
  (idEE := inductive_map (inl_system_product si1) (inl_product_can_fun SE SE')
         (E \times E'))
  (idFF := inductive_map (inl_system_product si3) (inl_product_can_fun SF SF')
         (F \times F')):
  [/\ bijection_prop idEE EE (E \times E'),
   bijection_prop idFF FF (F \times F'),
   function_prop (lu \ftimes lu') (E \times E') (F \times F'),
   function_prop luu EE FF &
   (lu \ftimes lu') \co idEE = idFF \co luu].
Proof.
move:(inl_product_can_fun_bij si1); rewrite /= -/E -/E' -/EE -/idEE => pa.
move:(inl_product_can_fun_bij si3); rewrite /= -/F -/F' -/FF -/idFF => pb.
move:(proj1 (inl_map2_prop si2 cu)); rewrite -/E -/F -/lu => lup.
move:(proj1 (inl_map2_prop inl_prod_si4 cu')).
rewrite -/E' -/F' -/lu'; move =>  lup'.
move: (ext_to_prod_fun_bis lup lup') =>  pc.
have si5: inl_same_index inl_prod_SEE inl_prod_SFF by [].
move: (proj1 (inl_map2_prop si5 inl_prod_uu_prop)).
rewrite -/EE -/FF -/luu => pd.
split => //.
move:pa pb => [[[fiE _] _] siE tiE] [[[fiF _] _] siF tiF].
move:pc pd => [fh sh th] [fb sb tb].
have cop1: lu \ftimes lu' \coP idEE by split => //; ue.
have cop2: idFF \coP luu by  split => //; ue.
apply: function_exten.
- by apply:compf_f.
- by apply:compf_f.
- aw; ue.
- aw; ue.
- aw; rewrite siE => x xE.
  have xs1:inc x (source luu) by ue.
  have xs2: inc x (source idEE) by ue.
  move:lup lup' => [fu su tu][fu' su' tu'].
  rewrite ! compfV //.
  move/inductive_limit_hi: xE; move => /= [].
  set i := (Q (rep x)); set y := (P (rep x));move => iIE qb ->.
  have iIE': inc i (isI SE') by rewrite - (inl_same_index_same_I si1).
  have iIF: inc i (isI SF) by rewrite - (inl_same_index_same_I si2).
  have iIF': inc i (isI SF') by rewrite - (inl_same_index_same_I si3).
  have ra:= (inl_product_can_fun_compat si1).
  have ra':= (inl_product_can_fun_compat si3).
  rewrite  (inl_inductive_map_ev ra iIE qb).
  rewrite /inl_product_can_fun LgV//.
  move:(inl_can_fun_fp iIE) => [fcfi scfi tcfi].
  move:(inl_can_fun_fp iIE') => [fcfi' scfi' tcfi'].
  rewrite (inl_map_val_aux2 si5 inl_prod_uu_prop iIE qb).
  rewrite /inl_prod_uu LgV//.
  move:(proj43 cu i iIE) => [fui sui tui].
  move:(proj43 cu' i iIE') => [fui' sui' tui'].
  move:qb; rewrite /inl_product_E LgV// => qb.
  have ys:inc y (source (Vg u i) \times source (Vg u' i)) by rewrite sui sui'.
  rewrite  (ext_to_prod_V2 fui fui' ys).
  move: (qb); rewrite - scfi - scfi' => qb'.
  move /setX_P: qb => [py Py Qy].
  have rx:inc (J (Vf (Vg u i) (P y)) (Vf (Vg u' i) (Q y)))
      (Vg (isE (inl_system_product si3)) i).
    rewrite /= /inl_product_E LgV//; apply:setXp_i; Wtac.
  rewrite (inl_inductive_map_ev ra' iIF rx).
  rewrite /inl_product_can_fun !LgV//.
  move: (inl_can_fun_fp iIF) => [fcfi''' scfi''' tcfi'''].
  move: (inl_can_fun_fp iIF') => [fcfi'''' scfi'''' tcfi''''].
  have rb: inc (Vf (Vg u i) (P y)) (Vg (isE SF) i) by Wtac.
  have rc: inc (Vf (Vg u' i) (Q y)) (Vg (isE SF') i) by Wtac.
  rewrite (ext_to_prod_V fcfi''' fcfi''''); try ue.
  rewrite (inl_can_fun_ev iIF rb) (inl_can_fun_ev iIF' rc). 

  rewrite (ext_to_prod_V2 fcfi fcfi' qb').
  rewrite (inl_can_fun_ev iIE  Py) (inl_can_fun_ev iIE'  Qy).
  have rb':= (inl_class_in_lim iIE Py).
  have rc':=(inl_class_in_lim iIE' Qy).
  have si4:= inl_prod_si4. 
  rewrite (ext_to_prod_V fu fu'); try ue.
  rewrite (inl_map_val_aux2 si2 cu iIE Py)  (inl_map_val_aux2 si4 cu' iIE' Qy).
  done.
Qed.
   
  
End InjectiveProductMap.

Section ProjectiveLimitNoId.
Variables E I r f: Set.
Hypothesis 
  (preorder_r:  preorder r)
  (substrate_r:  substrate r = I)
  (fgraph_E: fgraph E)
  (domain_E: domain E = I)
  (fgraph_f: fgraph f)
  (domain_f: domain f = r)
  (function_f:
    forall i, inc i r ->
               function_prop (Vg f i) (Vg E (Q i)) (Vg E (P i)))
  (compose_f: forall i  j k, gle r i j -> gle r j k ->
                  Vg f (J i j) \co  Vg f (J j k) = Vg f (J i k)).

Definition noid_projlim :=
  Zo (productb E) (fun x => forall  i j, gle r i j
                               -> (Vg x i) = Vf (Vg f (J i j)) (Vg x j)).


Definition noid_E  :=  Lg I (fun i => Imf (Vg f (J i i))).
Definition noid_f := Lg r (fun z => restriction2 (Vg f z) 
   (Vg noid_E (Q z))  (Vg noid_E (P z))).

Lemma noid_prop0 i: inc i I -> sub (Vg noid_E i) (Vg E i).
Proof.
move => iI.
rewrite /noid_E; aw.
  have ii: inc (J i i) r by apply: (proj32 preorder_r i); rewrite substrate_r.
  case:(function_f ii);  aw => ff sf <-; rewrite LgV//.
  apply: (Imf_Starget ff).
Qed.

  
Lemma noid_prop1 (M:= noid_E) (g := noid_f):
  [/\ 
   forall z, inc z r -> 
      restriction2_axioms (Vg f z) (Vg M (Q z)) (Vg M (P z)),
   forall i j x, gle r i j -> inc x (Vg M j) ->
     Vf (Vg g (J i j)) x = Vf (Vg f (J i j)) x,
   forall i, inc i r -> function_prop (Vg g i) (Vg M (Q i)) (Vg M (P i)),
   forall i j k, gle r i j -> gle r j k ->
                 Vg g (J i j) \co  Vg g (J j k) = Vg g (J i k) &
   forall i, inc i I -> Vg g (J i i) = identity (Vg M i)].
Proof.
have rc z: inc z r ->
       restriction2_axioms (Vg f z) (Vg M (Q z)) (Vg M (P z)).
  move => zr.
  move:(function_f zr) =>[ff sf tf].
  move: (pr1_sr zr)(pr2_sr zr); rewrite substrate_r => iI jI.
  move:(noid_prop0 jI); rewrite /M /noid_E ! LgV// - sf =>  hu.
  split.
  - done.
  - done.
  - rewrite tf; move:(noid_prop0 iI); rewrite /noid_E LgV//.
  - have pz:= ((proj31 preorder_r) _ zr).
    move => t /(Vf_image_P ff hu) [u uif ->].
    move:(zr); rewrite - pz => zr'.
    have ii: inc (J(P z) (P z)) r
        by apply: (proj32 preorder_r (P z)); rewrite substrate_r.
    have jj: inc (J(Q z) (Q z)) r
        by apply: (proj32 preorder_r (Q z)); rewrite substrate_r.
   case:(function_f ii); aw => fii sii tii.
   case:(function_f jj); aw => fjj sjj tjj.
   have co1: Vg f z \coP Vg f (J (Q z) (Q z)) by split => //; ue.
   have co2: Vg f (J (P z) (P z)) \coP Vg f z  by split => //; ue.
   move/(Imf_P fjj):uif => [v]; rewrite sjj => vej  vv.
   apply/(Imf_P fii); rewrite sii vv.
   exists (Vf (Vg f z) v); first Wtac.
   move:(compose_f ii zr') (compose_f zr' jj); rewrite pz => eqa eqb.
   move:(f_equal (Vf ^~ v) eqa)(f_equal (Vf ^~ v) eqb). 
  rewrite !compfV //; try ue; move => -> //.
have rd:forall i j x, gle r i j -> inc x (Vg M j) ->
     Vf (Vg g (J i j)) x = Vf (Vg f (J i j)) x.
  move => i j x lij xm.
  have hb':inc x (Vg M (Q (J i j))) by aw.
  rewrite /g /noid_f -(restriction2_V  (rc _ lij) hb'); rewrite LgV//.
have re i: inc i r -> function_prop (Vg g i) (Vg M (Q i)) (Vg M (P i)).
  move => ir; rewrite /g/noid_f LgV//.
  exact: (restriction2_prop (rc _ ir)).
have rg i: inc i I -> Vg g (J i i) = identity (Vg M i).
  move => iI.
  have ii: inc (J i i) r by apply: (proj32 preorder_r i); rewrite substrate_r.
  move:(compose_f ii ii) => cc.
  move:(function_f ii); aw; move => [ff sf tf].
  move:(re _ ii); aw => fp; apply: (identity_prop0 fp) => x xM.
  rewrite (rd _ _  _ ii xM). 
  move:xM; rewrite /M /noid_E LgV//; move/(Imf_P ff); rewrite sf.
  move => [u uE ->]; rewrite - {3}cc; rewrite compfV //; [ split => //; ue | ue ].
split => // i j k lij ljk.
have lik: gle r i k by apply: (proj33 preorder_r) lij ljk. 
move: (re _ lij) => [fij sij tij].
move: (re _ ljk) => [fjk sjk tjk].
move: (re _ lik) => [fik sik tik].
rewrite ! pr1_pair in tij tik tjk.
rewrite ! pr2_pair in sij sik sjk.
have co1:  Vg g (J i j) \coP Vg g (J j k) by  split => //; rewrite sij tjk.
have fc1: function (Vg g (J i j) \co Vg g (J j k)) by apply: compf_f.
apply: function_exten => //.
- by aw; rewrite sik sjk.
- by aw; rewrite tij tik.
aw; rewrite sjk => x xM.
have cpp: Vg f (J i j) \coP Vg f (J j k). 
  move: (function_f lij) => [fa fb fc].
  move: (function_f ljk) => [fa' fb' fc'].
  by split => //; rewrite fb fc'; aw.
have vm: inc (Vf (Vg g (J j k)) x) (Vg M j).
  by rewrite - tjk; apply:(Vf_target fjk); rewrite sjk.
have xM': inc x (source (Vg f (J j k))). 
  have kI: inc k I by rewrite  - substrate_r; order_tac.
  move: (function_f ljk) => [_ -> _]; aw.
  by apply:(noid_prop0 kI).
have xM'':  inc x (source (Vg g (J j k))) by rewrite sjk.
rewrite (rd _ _ _ lik xM) - (compose_f lij ljk).
by rewrite !compfV //(rd _ _ _ lij vm) (rd _ _ _ ljk xM). 
Qed.

Definition noid_proj_system: projective_system.
Proof.
apply:(@ProjectiveSystem  noid_E I r noid_f).
- exact.
- exact.
- rewrite/noid_E; fprops.
- by rewrite /noid_E; aw.
- by rewrite /noid_f; fprops.
- by rewrite /noid_f; aw.
- by case: (noid_prop1).
- by case: (noid_prop1).
- by case: (noid_prop1).
Defined.

Lemma noid_prop2: projective_system_on noid_proj_system  noid_E I r noid_f.
Proof.  done. Qed.

Lemma noid_prop3 : projective_limit(noid_proj_system) = noid_projlim.
Proof.
move:(noid_prop1) => [Ha Hb Hc Hd He].
have dd: domain E = domain noid_E by rewrite /noid_E Lgd.
set_extens t.
  move/prl_limitP => /= [ta tb tc td]; apply /Zo_P; split.
    apply/setXb_P; split => //.
      by rewrite tb .
    by move => i; rewrite domain_E => iI; apply:(noid_prop0 iI); apply: tc.
  move => // i j lij.
  have xM: inc (Vg t j) (Vg noid_E j).
    by apply: tc; rewrite - substrate_r; order_tac.
  by move: (td _ _ lij); rewrite (Hb _ _ _ lij xM). 
move =>/Zo_P [ /setXb_P [ta tb tc] td].
have Hf i: inc i I ->  inc (Vg t i) (Vg noid_E i).
  move => iI; rewrite /noid_E LgV//.
  have ii: inc (J i i) r by apply: (proj32 preorder_r i); rewrite substrate_r.
  rewrite (td _ _ ii).
  case: (function_f ii); aw => [ff sf tf].
  apply/(Imf_P ff); exists (Vg t i) => //; rewrite sf; apply: tc;ue.
apply/prl_limitP => /=; split => //; first ue.
move => i j lij. rewrite (td _ _ lij)(Hb _ _ _ lij) //; apply: Hf.
rewrite - substrate_r; order_tac.
Qed.
End ProjectiveLimitNoId.



Section InductiveLimitNoId.

Variables E I r f: Set.
Hypothesis 
  (preorder_r:  preorder r)
  (substrate_r:  substrate r = I)
  (directed_r: right_directed_on r I)
  (fgraph_E: fgraph E)
  (domain_E: domain E = I)
  (fgraph_f: fgraph f)
  (domain_f: domain f = r)
  (function_f:
    forall p, inc p r ->
              function_prop (Vg f p) (Vg E (P p)) (Vg E (Q p)))
  (compose_f: forall i  j k, gle r i j -> gle r j k ->
                  Vg f (J j k) \co  Vg f (J i j) = Vg f (J i k)).


Definition noid_E'  :=  Lg I (fun i => Imf (Vg f (J i i))).
Definition noid_g := Lg r (fun z => restriction2 (Vg f z) 
   (Vg noid_E' (P z))  (Vg noid_E' (Q z))).


Lemma noid_prop5a i: inc i I -> sub (Vg noid_E' i) (Vg E i).
Proof.
move => iI.
rewrite /noid_E'; aw.
have ii: inc (J i i) r by apply: (proj32 preorder_r i); rewrite substrate_r.
case:(function_f ii); aw; move => ff df <-; rewrite LgV//.
apply: (Imf_Starget ff).
Qed.


Lemma noid_prop5b z: inc z r ->
       restriction2_axioms (Vg f z) (Vg noid_E' (P z)) (Vg noid_E' (Q z)).
Proof.
move => zr.
move:(function_f zr) =>[ff sf tf].
move: (pr1_sr zr)(pr2_sr zr); rewrite substrate_r => iI jI.
move:(noid_prop5a iI); rewrite /noid_E' LgV// - sf =>  hu.
split.
- done.
- done.
- rewrite tf; move:(noid_prop5a jI); rewrite /noid_E' LgV//.
- have pz:= ((proj31 preorder_r) _ zr).
  move => t /(Vf_image_P ff hu) [u uif ->].
  move:(zr); rewrite - pz => zr'.
  have ii: inc (J (P z) (P z)) r
    by apply: (proj32 preorder_r (P z)); rewrite substrate_r.
  have jj: inc (J(Q z) (Q z)) r
    by apply: (proj32 preorder_r (Q z)); rewrite substrate_r.
  case:(function_f ii); aw => fii sii tii.
  case:(function_f jj); aw => fjj sjj tjj.
  have co1: Vg f z \coP Vg f (J (P z) (P z)) by split => //; ue.
  have co2: Vg f (J (Q z) (Q z)) \coP Vg f z  by split => //; ue.
  move/(Imf_P fii):uif => [v]; rewrite sii => vej  vv.
  rewrite LgV//; apply/(Imf_P fjj); rewrite sjj vv.
  exists (Vf (Vg f z) v); first Wtac.
  move:(compose_f ii zr') (compose_f zr' jj); aw; rewrite pz => eqa eqb.
  move:(f_equal (Vf ^~ v) eqa)(f_equal (Vf ^~ v) eqb).
  rewrite !compfV //;try ue; move => -> //.
Qed.

Lemma noid_prop5c i j x: gle r i j -> inc x (Vg noid_E' i) ->
     Vf (Vg noid_g (J i j)) x = Vf (Vg f (J i j)) x.
Proof.
move => lij xm.
have hb':inc x (Vg noid_E' (P (J i j))) by aw.
rewrite /noid_g -(restriction2_V  (noid_prop5b lij) hb') LgV//.
Qed.


Lemma noid_prop5d i: inc i r ->
  function_prop (Vg noid_g i) (Vg noid_E' (P i)) (Vg noid_E' (Q i)).
Proof.
move => ir; rewrite /noid_g LgV//.
exact: (restriction2_prop (noid_prop5b ir)).
Qed.

Lemma noid_prop5e i: inc i I -> Vg noid_g (J i i) = identity (Vg noid_E' i).
Proof.
move => iI.
have ii: inc (J i i) r by apply: (proj32 preorder_r i); rewrite substrate_r.
move:(compose_f ii ii) => cc.
move:(function_f ii); aw; move => [ff sf tf].
move:(noid_prop5d  ii); aw => fp; apply: (identity_prop0 fp) => x xM.
rewrite (noid_prop5c ii xM). 
move:xM; rewrite /noid_E' LgV//;  move/(Imf_P ff); rewrite sf.
move => [u uE ->]; rewrite - {3}cc compfV //; [ split => //; ue | ue ].
Qed.

Lemma  noid_prop5f i j k:  gle r i j -> gle r j k ->
  Vg  noid_g (J j k) \co  Vg noid_g (J i j) = Vg noid_g (J i k).
Proof.
move => lij ljk.
have lik: gle r i k by apply: (proj33 preorder_r) lij ljk. 
move: (noid_prop5d lij) => [fij sij tij].
move: (noid_prop5d ljk) => [fjk sjk tjk].
move: (noid_prop5d lik) => [fik sik tik].
rewrite ! pr2_pair in tij tik tjk.
rewrite ! pr1_pair in sij sik sjk.
have co1:  Vg noid_g (J j k) \coP Vg noid_g (J i j).
  by split => //; rewrite tij sjk.
have fc1: function(Vg noid_g (J j k) \co Vg noid_g (J i j)) by apply: compf_f.
apply: function_exten => //.
    by aw; rewrite sij sik.
  by aw; rewrite tjk tik.
aw; rewrite sij => x xM.
have xM'':inc x (source (Vg noid_g (J i j))) by rewrite sij.
have cpp: Vg f (J j k) \coP Vg f (J i j). 
  move: (function_f lij) => [fa fb fc].
  move: (function_f ljk) => [fa' fb' fc'].
  by split => //; rewrite fb' fc; aw.
have xM': inc x (source (Vg f (J i j))). 
  have iI: inc i I by rewrite  - substrate_r; order_tac.
  move: (function_f lij) => [_ -> _]; aw.
  by apply:(noid_prop5a iI).
have : inc (Vf (Vg noid_g (J i j)) x) (Vg noid_E' j).
  by rewrite - tij; apply:(Vf_target fij); rewrite sij.
rewrite (noid_prop5c lij xM) => xM2.
rewrite (noid_prop5c lik xM) -(compose_f lij ljk).
by rewrite !compfV //(noid_prop5c lij xM) (noid_prop5c ljk xM2). 
Qed.

Lemma noid_prop5g y i j k: 
  gle r i j -> gle r j k -> inc y (Vg E i) ->
  Vf (Vg f (J j k))  (Vf (Vg f (J i j)) y) = Vf (Vg f (J i k)) y.
Proof.
move => lij ljk yEi.
move:(function_f lij)(function_f ljk); aw; move =>[fa sa ta][fb sb tb].
have cop:Vg f (J j k) \coP  Vg f (J i j) by split => //; ue.
move:(f_equal (Vf^~ y) (compose_f lij ljk)); rewrite  compfV //; ue.
Qed.


Definition noid_ind_system: inductive_system.
Proof.
apply:(@InductiveSystem  noid_E' I r noid_g).
- exact.
- exact.
- exact.
- rewrite /noid_E'; fprops.
- by rewrite /noid_E'; aw.
- rewrite /noid_g; fprops.
- by rewrite /noid_g; aw.
- apply:  noid_prop5d.
- apply:  noid_prop5f.
- apply:  noid_prop5e.
Defined.


Lemma noid_prop6:  inductive_system_on noid_ind_system  noid_E' I r noid_g.
Proof.  done. Qed.


Definition noid_inl_sum := disjointU E.

Definition noid_inl_equiv_rel x y:=
  exists k, [/\ gle r (Q x) k,  gle r (Q y) k   &
   Vf (Vg f (J (Q x) k)) (P x) =  Vf (Vg f (J (Q y) k)) (P y) ].

Definition noid_inl_equiv  := graph_on noid_inl_equiv_rel noid_inl_sum.
Definition noid_limit := quotient noid_inl_equiv.


Lemma noid_inl_sumP x: inc x noid_inl_sum <->
  [/\ pairp x, inc (Q x) I & inc (P x) (Vg E (Q x))].
Proof.
split; first by case/disjointU_P; rewrite domain_E. 
by move => [ha hb hc]; apply /disjointU_P; rewrite domain_E. 
Qed.

Lemma noid_inl_equiv_reflexive a: inc a noid_inl_sum -> noid_inl_equiv_rel a a.
Proof.
move/noid_inl_sumP => [ _ pb _].
have pa: gle r (Q a) (Q a) by apply:(proj32 preorder_r); rewrite substrate_r.
by exists (Q a).
Qed.

Lemma noid_inl_equiv_esr: equivalence_on noid_inl_equiv noid_inl_sum.
Proof.
split; last by apply: graph_on_sr; apply:noid_inl_equiv_reflexive.
have ->: noid_inl_equiv = graph_on (fun a b =>
   [/\ inc a noid_inl_sum, inc b noid_inl_sum & 
    noid_inl_equiv_rel a b]) noid_inl_sum.
  by apply: Zo_exten1 => t /setX_P [_ px qx]; split => // [] [_ _].
apply: equivalence_from_rel; split.
  by move => x y [xs ys [k [ha hb hc]]]; split => //;exists k; split.
move=> y x z [xE yE [k [lxik lyik vfxik_yik]]] [_ zE [l [lyil lzil vfyil_zil]]].
split => //.
move: (arg2_sr lxik)(arg2_sr lyil); rewrite substrate_r => kI lI.
move:(directed_r kI lI) => [i [ iI lki lli]].
exists i; split => //.
- exact:(proj33 preorder_r _ _ _ lxik lki).
- exact:(proj33 preorder_r _ _ _ lzil lli).
move/noid_inl_sumP: xE => [_ aI xE].
move/noid_inl_sumP: yE => [_ bI yE].
move/noid_inl_sumP: zE => [_ cI zE].
move: (noid_prop5g lxik  lki xE) (noid_prop5g lyik  lki yE).
rewrite vfxik_yik ; move => -> ->.
move: (noid_prop5g lyil  lli yE) (noid_prop5g lzil lli zE).
by rewrite vfyil_zil; move => ->.
Qed.

Lemma noid_inl_class_eq x y:
  inc x noid_inl_sum -> inc y noid_inl_sum ->
  (class noid_inl_equiv x = class noid_inl_equiv y
     <-> noid_inl_equiv_rel x y).
Proof.
have [ha hb] := noid_inl_equiv_esr.
move => xE yE; move: (xE)(yE); rewrite - hb => xsr ysr.
split => xx.
  by move/(related_equiv_P ha): (And3 xsr ysr xx) => /graph_on_P1 [].
by apply/(class_eq1 ha); apply/graph_on_P1.
Qed.  

Lemma noid_inl_class_ii i x (y := Vf (Vg f (J i i)) x):
  inc i I -> inc x (Vg E i) ->
  [/\ inc y (Vg noid_E' i),
     inc (J x i) noid_inl_sum, inc (J y i) noid_inl_sum  &
  class noid_inl_equiv (J x i) = class noid_inl_equiv (J y i)].
Proof.
move => iI xEi.
have iir: inc (J i i) r by apply:(proj32 preorder_r); ue.
case:(function_f iir); aw=> [fii sii tii].
have yE: inc y (Vg E i) by rewrite /y ; Wtac.
have yE': inc y (Vg noid_E' i).
  by  rewrite / noid_E' LgV//; apply/(Imf_P fii); exists x => //; ue.
have xS: inc (J x i) noid_inl_sum.
  apply/noid_inl_sumP; split;aww.
have yS: inc (J y i) noid_inl_sum.
  apply/noid_inl_sumP; split;aww.
split => //; apply/(noid_inl_class_eq xS yS).
by exists i; aw;split => //; rewrite -(noid_prop5g iir iir xEi).
Qed.  

Lemma noid_inl_class_compat i j x y (R := (inl_equiv noid_ind_system) ):
  inc i I -> inc j I -> inc x (Vg noid_E' i) -> inc y (Vg noid_E' j) ->
   (class R (J x i) = class R (J y j) <->
    class noid_inl_equiv (J x i) =  class noid_inl_equiv (J y j)).
Proof.
move => iI jI xE yE.
move:(@inl_class_eq_bis noid_ind_system i j x y) => /= h.
apply: (iff_trans (h iI jI xE yE)); clear h.
have xixU: inc (J x i) noid_inl_sum.
 by apply/noid_inl_sumP;split; aw; fprops; apply: noid_prop5a.
have yjxU: inc (J y j) noid_inl_sum.
 by apply/noid_inl_sumP;split; aw; fprops; apply: noid_prop5a.
move:noid_inl_equiv_esr => [Er Sr].
split.
  move=> [k /= []]; aw; move => leik lejk.
  rewrite (noid_prop5c leik xE) (noid_prop5c lejk yE) => vv.
  apply:(class_eq1 Er); apply/graph_on_P1; split => //.
  - by exists k; aw.
rewrite - Sr in xixU yjxU => xx.
move/ (related_equiv_P Er): (And3 xixU yjxU xx) => /graph_on_P1 [_ _].
move =>[k []]; aw =>leik lejk etc; exists k; simpl; saw.
by rewrite  (noid_prop5c leik xE) (noid_prop5c lejk yE). 
Qed.
                                                                 
    
Definition noid_can x :=  class noid_inl_equiv (J (P (rep x)) (Q (rep x))).

Lemma noid_inl_prop7 (A := inductive_limit noid_ind_system) (B:= noid_limit):
 bijection_prop (Lf noid_can A B) A B.
Proof.
move:noid_inl_equiv_esr => [Er Sr].
saw; apply: lf_bijective.
- move => x /inductive_limit_hi /= [ha hb hc].
  apply:inc_class_setQ; rewrite (proj2  noid_inl_equiv_esr).
  by apply/noid_inl_sumP; aw; split; fprops;apply:noid_prop5a. 
- move => u v /inductive_limit_hi /= [ha hb hc]
            /inductive_limit_hi /= [ha' hb' hc'].
  rewrite {2} hc {2} hc' /noid_can.
  by move/(noid_inl_class_compat ha ha' hb hb').
- move => y /(setQ_P Er)[]; rewrite Sr; move/noid_inl_sumP.
  set i := Q _; set z := P _; move => [pry iI zE] yv.
  move: (noid_inl_class_ii iI zE)=> [qa qb qc qd].
  rewrite yv - pry qd /noid_can.
  set t := (Vf (Vg f (J i i)) z).
  set c :=  (class (inl_equiv noid_ind_system) (J t i)).
  have cA: inc c A by apply: inl_class_in_lim.
  move/inductive_limit_hi: (cA) => /= [ra rb rc].
  by ex_tac; apply/(noid_inl_class_compat iI ra qa rb).
Qed.


End InductiveLimitNoId.

(**  Exercises *)


Section Exercise1.

Variables I rI L rL Jf: Set.
Variable S: projective_system.

Hypothesis rS: (psr S = rI).
Hypotheses (HIp :preorder rI) (HIs: substrate rI = I).
Hypotheses (HLp :preorder rL) (HLs: substrate rL = L)
           (HLd:right_directed_prop rL).
Hypothesis (HJg: fgraph Jf) (HJd: domain Jf = L) (HJI: unionb Jf = I)
   (HJm: forall i j, gle rL i j -> sub (Vg Jf i) (Vg Jf j)).

Lemma ex1_prop1 i: inc i L -> sub (Vg Jf i) I.
Proof.
by rewrite - HJI => iL t tu; apply/setUb_P; rewrite HJd; ex_tac.
Qed.

Lemma ex1_prop2 i j: gle rL i j -> inc i L /\ inc j L.
Proof. by move => lij; move:(arg1_sr lij) (arg2_sr lij); rewrite HLs. Qed.

Lemma ex1_prop3: I = psI S.
Proof. by rewrite - HIs - ps_substrate_r rS. Qed.

Lemma ex1_prop4 i: inc i L -> sub (Vg Jf i) (psI S).
Proof. by move =>/ex1_prop1; rewrite ex1_prop3. Qed.

Lemma ex1_preorder i (ri:= induced_order rI (Vg Jf i)): 
   ( forall k, inc k L -> forall i j, inc i (Vg Jf k) ->  inc j (Vg Jf k) -> 
     exists t, [/\  inc t (Vg Jf k), gle rI i t & gle rI j t])  ->
   inc i L ->
  [/\ preorder ri, substrate ri = (Vg Jf i) & right_directed_prop ri].
Proof.
move => h' h.
have pa : sub (Vg Jf i) (substrate rI) by rewrite HIs; apply:(ex1_prop1 h).
have pb:= (ipreorder_sr HIp pa).
have pc:= iorder_preorder pa HIp.
split => // a b; rewrite pb => ai bi.
move:(h' _ h _ _ ai bi) => [c [ci ca cb]].
by exists c; split; [apply/(iorder_gle0P rI ai ci)|apply/(iorder_gle0P rI bi ci)].
Qed.

Definition ex1_systemi i:=
  match (ixm (inc i L)) with
    | inl hx => (prl_restr (ex1_prop4 hx))
    | inr _ => S
end.

Definition ex1_Fl i := projective_limit(ex1_systemi i).
Definition ex1_gij ij :=
  Lf (restr ^~ (Vg Jf (P ij))) (ex1_Fl (Q ij)) (ex1_Fl (P ij)). 

Lemma ex1_res0 i (H: inc i L):
  ex1_Fl i = (projective_limit (prl_restr (ex1_prop4 H))).
Proof.
by rewrite /ex1_Fl /ex1_systemi;case: (ixm (inc i L)).
Qed.

       
Lemma ex1_prop5a j: inc j L -> (Vg Jf j) = psI (ex1_systemi j).
Proof. by move => jL; rewrite /ex1_systemi; case: (ixm (inc j L)).  Qed.

Lemma ex1_prop5b i (H: sub (Vg Jf i) (psI S)):
  inc i L -> prl_same_data (prl_restr H) (ex1_systemi i).
Proof. by move => iL;rewrite /ex1_systemi; case: (ixm (inc i L)). Qed.

Lemma ex1_prop5 i j: gle rL i j ->  sub (Vg Jf i) (psI (ex1_systemi j)).
Proof.
move => lij;rewrite - (ex1_prop5a (proj2 (ex1_prop2 lij))); exact:(HJm lij).
Qed.

Lemma ex1_prop6 i j  (lij: gle rL i j) :
  prl_same_data (prl_restr (ex1_prop5 lij)) (ex1_systemi i).
Proof.
have r1 := HJm lij.
have [iL jL]:= (ex1_prop2 lij).
have Hu:= (ex1_prop4 jL).
apply:prl_same_dataT (ex1_prop5b  (sub_trans r1 Hu) iL).
apply:prl_same_dataT  (projective_limit_restr_double_Iv Hu  r1).
apply:prl_restr_Iv2.
exact: (prl_same_dataS (ex1_prop5b Hu jL)).
Qed.

Lemma ex1_prop6a i j  (lij: gle rL i j) :
  (projective_limit_restr (ex1_prop5 lij)) = (ex1_Fl i).
Proof. apply:projective_limit_Iv;apply:ex1_prop6. Qed.

Lemma ex1_prop7 i j: gle rL i j ->
  lf_axiom (restr^~ (Vg Jf i)) (ex1_Fl j) (ex1_Fl i).
Proof.
move => lij; move: (prl_restr_canonical_ax (ex1_prop5 lij)).
by rewrite (ex1_prop6a lij).
Qed.

Lemma ex1_res2 i j: gle rL i j ->
  function_prop (ex1_gij (J i j))  (ex1_Fl j) (ex1_Fl i).
Proof.
move =>/ex1_prop7/lf_function ff; rewrite/ex1_gij; saw. 
Qed.

Lemma ex1_res3 i: inc i L -> ex1_gij (J i i) = identity (ex1_Fl i).
Proof.
move => iL; rewrite /ex1_gij pr1_pair pr2_pair ex1_res0.
apply:prl_restr_trivial.
Qed.

Lemma ex1_pr4 i j k: gle rL i j ->   gle rL j k ->
   ex1_gij (J i j) \co ex1_gij (J j k) = ex1_gij (J i k).
Proof.
move => lij ljk; move: (proj33 HLp _ _ _ lij ljk) => lik.
move:(ex1_res2 lij) => [fij sij tij].
move:(ex1_res2 lik) => [fik sik tik].
move:(ex1_res2 ljk) => [fjk sjk tjk].
have cop: ex1_gij (J i j) \coP ex1_gij (J j k).
  by split => //; rewrite sij tjk.
apply:function_exten.
- by apply:compf_f.
- exact.
- by aw; rewrite sjk sik.
- by aw; rewrite tij tik. 
- aw; rewrite sjk => x s.
  move:(ex1_prop7 lij)(ex1_prop7 lik)(ex1_prop7 ljk) => aij aik ajk. 
  have xs': inc x (source (ex1_gij (J j k)))  by rewrite sjk.
  rewrite compfV// /ex1_gij; aw; rewrite ! LfV//.
    by rewrite (double_restr _ (HJm lij)).
  aw; apply: ajk; ue.
Qed.

Definition ex1_F: projective_system.
Proof.
apply:(@ProjectiveSystem (Lg L ex1_Fl) L rL (Lg rL ex1_gij)).
- exact: HLp.
- exact:HLs.
- fprops.
- by aw.
- by fprops.
- by aw.
- move => p pL; move: (proj31 HLp _ pL) => pp. 
  move:(pr2_sr pL) (pr1_sr pL); rewrite HLs => iL jL.
  rewrite !LgV//;move:pL;rewrite -{1 2}pp => pL; apply: (ex1_res2 pL).
- move => i j k ha hb; rewrite !LgV//; first by apply:(ex1_pr4 ha hb).
  exact: (proj33 HLp _ _ _ ha hb).
- move => i iL; move: (iL); rewrite -HLs => iL'.
  move:(proj32 HLp _ iL') => ii.
  rewrite !LgV//; exact:(ex1_res3 iL).
Defined.


Lemma ex1_F_prop: projective_system_on ex1_F (Lg L ex1_Fl) L rL (Lg rL ex1_gij).
Proof. done. Qed.

Definition ex1_restr_fun z:=  Lg L (fun i => restr z (Vg Jf i)).

Definition ex1_F_can := Lf ex1_restr_fun
   (projective_limit S) (projective_limit ex1_F). 

Lemma ex1_F_can_ax1 i z: inc i L -> inc z (projective_limit S) ->
   inc (restr z (Vg Jf i)) (ex1_Fl i).
Proof.
move => iL zp; move:(prl_restr_canonical_ax(ex1_prop4 iL) zp).
by congr inc; apply:projective_limit_Iv; apply:ex1_prop5b.
Qed.

Lemma ex1_F_can_ax: lf_axiom ex1_restr_fun
   (projective_limit S) (projective_limit ex1_F). 
Proof.
move:ex1_F_prop => [E_F I_F r_F f_F].
move => z zp.
move/prl_limitP:(zp) => [fgz dz zv zw].
rewrite /ex1_restr_fun;apply/prl_limitP; split.
- fprops.
- by aw.
- by rewrite E_F;move => i iL; rewrite !LgV//; apply: ex1_F_can_ax1.
- rewrite r_F f_F;move => i j lij.
  have[iL jL] := ex1_prop2 lij.
  move: (HJm  lij) => s1.
  move: (ex1_prop7 lij) (ex1_F_can_ax1 jL zp) => ra rb.
  rewrite /ex1_restr_fun/ex1_gij. rewrite LgV// LgV// LgV//; aw.
  by rewrite LfV// double_restr.
Qed.

Lemma ex1_F_can_fun: function_prop ex1_F_can
 (projective_limit S) (projective_limit ex1_F). 
Proof.
rewrite /ex1_F_can; saw.
by apply:lf_function; apply: ex1_F_can_ax.
Qed.


Lemma ex1_F_can_bf: bijection ex1_F_can.
Proof.
rewrite /ex1_F_can;apply:lf_bijective; first by apply: ex1_F_can_ax.
  move => u v upl vpl sr.
  move/prl_limitP:upl => [fgu du uv uw].
  move/prl_limitP:vpl => [fgv dv vv vw].
  have sdu: domain u = domain v by rewrite du dv.
  apply:(fgraph_exten fgu fgv sdu);rewrite du  - ex1_prop3 - HJI.
  move => j /setUb_P [k kdj jv]; rewrite HJd in kdj.
  move: (f_equal (Vg ^~k) sr); rewrite/ex1_restr_fun LgV// => sr'.
  by move: (f_equal (Vg ^~j) sr'); rewrite !LgV//.
move => y yp.
have HL3 i j: inc i L -> inc j L -> 
  exists k, [/\ inc k L, gle rL i k & gle rL j k].
  move => iL jL.
  have isr: inc i (substrate rL) by rewrite HLs.
  have jsr: inc j (substrate rL) by rewrite HLs.
  move:(HLd isr jsr) => [k [i1k i2k]].
  move:(arg2_sr i1k); rewrite HLs => kL; by exists k.
move:ex1_F_prop => [E_F I_F r_F f_F].
have da: domain (psE ex1_F) = L by  rewrite E_F; aw.
move/Zo_P:(yp)  => [/setXb_P [fgy dy yv] yw].
rewrite da in dy yv; rewrite r_F in yw.
have yab a b: gle rL a b -> Vg y a = restr (Vg y b) (Vg Jf a).
  move => lab;move: (yw _ _ lab); rewrite f_F LgV//.
  have bsr:= (proj2 (ex1_prop2 lab)).
  move:(ex1_prop7 lab) => ax1.
  rewrite/ex1_gij; aw; rewrite LfV//.
  move: (yv b bsr); rewrite E_F LgV//.
have ha i j1 j2: inc j1 L -> inc j2 L -> inc i (Vg Jf j1) -> inc i (Vg Jf j2) 
  -> Vg (Vg y j1) i = Vg (Vg y j2) i.
  move => j1l j2l ij1 ij2.
  move:(HL3 _ _ j1l j2l) => [k [kL j1k j2k]].
  by rewrite (yab _ _ j1k) (yab _ _ j2k) ! LgV//.
pose idx i := choose (fun j => inc j L /\ inc i (Vg Jf j)).
have idx1p i: inc i I ->  inc (idx i) L /\ inc i (Vg Jf (idx i)).
  rewrite - HJI => /setUb_P [k ka kb].
  apply: (choose_pr (p:= (fun j => inc j L /\ inc i (Vg Jf j)))).
  by rewrite - HJd; exists k.
pose xi i := Vg (Vg y (idx i)) i.
have idx2 i j: inc j L -> inc i (Vg Jf j) -> xi i = Vg (Vg y j) i.
  move => jL ij; move: (idx1p _ (ex1_prop1 jL ij)) => [hu hv].
  by apply:ha.
set x := Lg I xi.
have xx i  (iL: inc i L):  
   inc (Vg y i) (projective_limit (prl_restr (ex1_prop4 iL))).
   move: (yv _ iL); rewrite  E_F LgV// /ex1_Fl /ex1_systemi.
   by case: (ixm (inc i L)).
have xpe: inc x (productb (psE S)).
   apply/setXb_P; rewrite /x ps_domain_E - ex1_prop3; split; aww.
   move => i iI; rewrite LgV//.
   move:(idx1p _ iI) => [sa sb]. 
   move: (xx _ sa); move /Zo_P. 
   move: (prl_restr_prop (ex1_prop4 sa)) =>[ka kb kc kd]; rewrite ka kc kd.
   move => [] /setXb_P [fgu]; aw; move => du uv _.
   by move: (uv _ sb); rewrite LgV.
have yve: y = ex1_restr_fun x.
  move/setXb_P: xpe =>[xa xb xc].
  rewrite /ex1_restr_fun;apply: fgraph_exten; aww.
  rewrite dy => i iL;move: (xx _ iL);move /Zo_P. 
  move: (prl_restr_prop (ex1_prop4 iL)) =>[ka kb kc kd]; rewrite ka kc kd.
  move => [] /setXb_P [fgu]; rewrite LgV//;aw; move => dyi yip1 yip2.
  apply: fgraph_exten => //; aww.
  rewrite dyi /x => j di; have jI:=(ex1_prop1 iL di).
  by rewrite ! LgV  //(idx2 _ _ iL di).
exists x => //; apply/Zo_P; split => //.
move => i j lij.
move:(arg1_sr lij) (arg2_sr lij); rewrite rS HIs => iI jI.
move:(idx1p _ iI) (idx1p _ jI) => [pa pb][pc pd].
rewrite /x /xi; rewrite !LgV //.
move:(HL3 _ _ pa pc) => [k [kL j1k j2k]].
have ii: inc i (Vg Jf k) by apply: (HJm j1k).
have jj: inc j (Vg Jf k) by apply: (HJm j2k).
rewrite (ha i (idx i) k pa kL pb ii).
rewrite (ha j (idx j) k pc kL pd jj).
have ll: gle(induced_order (psr S) (Vg Jf k)) i j by apply/iorder_gleP.
move: (xx _ kL) => /Zo_P [yp1 yp2].
rewrite (yp2 _ _ ll)/prl_restr /= LgV //.
Qed.


End Exercise1.


Lemma  Exercise7_2 S:
  right_directed  (psr S) ->
  (forall i j, gle (psr S) i j -> injection (Vg (psf S) (J i j))) ->
  forall i, inc i (psI S) -> injection (prl_can_fun S i).
Proof.
move => ha hb i iI.
have exi:=(prl_proj_ax iI).
move:(prl_can_fun_fp iI) => [ffi sfi tfi].
split => //; rewrite sfi => x y xpl ypl.
rewrite /prl_can_fun; rewrite !LfV// => svi.
move/prl_limitP: xpl => [fgx dx xv xw].
move/prl_limitP: ypl => [fgy dy yv yw].
apply: fgraph_exten => //; first by rewrite dx dy.
rewrite dx => j jde.
have isr: inc i (substrate (psr S)) by rewrite ps_substrate_r.
have jsr: inc j (substrate (psr S)) by rewrite ps_substrate_r.
move/right_directedP: ha => [_ h]; move:(h _ _ isr jsr)=> [k [ka kb]] {h}.
move: svi. rewrite (xw _ _ ka) (yw _ _ ka) (xw _ _ kb) (yw _ _ kb) => svk.
move:(ps_function_f ka) => [fik sik  tik].
have kk: inc k (psI S) by move:(arg2_sr ka); rewrite ps_substrate_r.
have xs1: inc  (Vg x k) (source (Vg (psf S) (J i k))).
  by rewrite sik pr2_pair; apply: xv. 
have ys1: inc  (Vg y k) (source (Vg (psf S) (J i k))).
  by rewrite sik pr2_pair; apply: yv.
by rewrite (proj2 (hb _ _ ka) _ _ xs1 ys1 svk).
Qed.

Section Exercise3.

Variables S S': projective_system.
Variable (u:Set).  
Hypothesis same_I: (prl_same_index S S').
Hypothesis (Hu: prl_map2_compat S S' u).

Lemma ex3_prl_subfm_hyp (S'' := prl_system_product  same_I):
  prl_subfam_hyp S'' (Lg (psI S) (fun i => graph (Vg u i))).
Proof.
move:(prl_system_product_prop same_I); rewrite -/S'' => -[ha hb hc hd].
have pr1 j:  inc j (psI S) ->
  sub (graph (Vg u j)) (Vg (psE S) j \times Vg (psE S') j).
  move => iI.
  by move: Hu=> [_ _ hu _];move: (hu _ iI) => [[[ _ qa] _ _ ] <- <-].
rewrite /prl_subfam_hyp; split; aww.
  rewrite hb ha; move => i iI; rewrite /prl_product_E; rewrite !LgV//; exact:pr1.
rewrite hc hd.
move => i j lij t. 
move: (prl_prop0 lij) => [iI jI].
rewrite /prl_product_f LgV//.
move: (Hu) =>[ _ _ _ h]; move:(h _ _ lij) => cc {h}.
move: (ps_function_f lij) => [fij sij tij].
rewrite same_I in lij.
move: (ps_function_f lij) => [fij' sij' tij'].
rewrite pr1_pair in tij tij';rewrite pr2_pair in sij sij'.
set f := _ \ftimes _.
have ff: function f by apply: ext_to_prod_f.
have sf: source f = (Vg (psE S) j \times Vg (psE S') j).
  by rewrite /f/ext_to_prod; aw; rewrite  sij sij'. 
have pr2: sub (graph (Vg u j)) (source f) by  rewrite sf; exact: pr1.
rewrite LgV//; move/(Vf_image_P ff pr2) => [w wg ->].
rewrite /f ext_to_prod_V2 //; last by rewrite sij sij' - sf;  apply: pr2.
move: Hu=> [_ _ hu _];move: (hu _ jI) => [fuj suj tuj].
move: (hu _ iI) => [fui sui tui].
move: (Vf_pr2 fuj wg) (p1graph_source1 fuj wg)  => qv pws.
have pws': inc (P w) (Vg (psE S) j).
  rewrite - suj; exact:  (p1graph_source1 fuj wg).
set x := (Vf (Vg (psf S) (J i j)) (P w)).
have xsi: inc x (source (Vg u i)) by rewrite sui /x - tij; Wtac.
rewrite LgV//;move: (Vf_pr3 fui xsi).
have -> //: (Vf (Vg u i) x) = (Vf (Vg (psf S') (J i j)) (Q w)).
have co1:  Vg (psf S') (J i j) \coP Vg u j by split => //;rewrite sij'.
have co2:  Vg u i \coP Vg (psf S) (J i j) by split => //; ue.
rewrite /x qv.
move/(f_equal (Vf ^~(P w))):cc; rewrite !compfV//; ue.
Qed.
  
Definition ex3limit_graphs := projective_system_subsets ex3_prl_subfm_hyp.
Definition ex3_graphs_limit := graph(projective_limit_fun S S' u).

Definition ex3_gl_val x := 
  Lg (psI S) (fun i => (J (Vg (P x) i) (Vg (Q x) i))).

Lemma  ex3_gl_val_ax:
  lf_axiom ex3_gl_val  ex3_graphs_limit (projective_limit ex3limit_graphs).
Proof.
move => t.
move:(prl_subsets_prop ex3_prl_subfm_hyp).
rewrite -/ex3limit_graphs; move => [s_E s_I s_r s_f].
move: (prl_map2_prop same_I Hu).
rewrite / ex3_graphs_limit; set f := projective_limit_fun _ _ _.
move => [[ff sf tf] fp] tgf.
move:(p1graph_source1 ff tgf) (p2graph_target1 ff tgf) (Vf_pr2 ff tgf).
rewrite sf tf => ps qt xv.
move: (Hu) => [hu1 hu2 hu3 hu4].
move/prl_limitP:(ps) => [pg pd pv pw].
apply/prl_limitP; rewrite s_E s_f /ex3_gl_val; split.
- fprops.    
- by aw. 
- aw => i iI; rewrite ! LgV//.
  move: (hu3 _ iI) => [fu su tu].
  have ha: inc (Vg (P t) i) (source (Vg u i)) by rewrite su; apply: pv.
  rewrite xv  -(prl_map_val_aux2 same_I Hu iI ps).
  exact: (Vf_pr3 fu ha).
- move:(prl_system_product_prop same_I) =>[s_E' s_I' s_r' s_f'].
move: (prl_subfam_prop1 ex3_prl_subfm_hyp).
rewrite s_r s_r'; set F := prl_subfam_fct _ _.
move => [qa qb qc qd qe].
move => i j lij.
move: (lij); rewrite same_I => lij'.
move: (prl_prop0 lij) => [iI jI].
move:(ps_function_f lij) =>[fij sij tij].
move:(ps_function_f lij') =>[fij' sij' tij'].
move/prl_limitP:(qt) => [qg q_d qv qw].
rewrite /ex3_gl_val LgV// LgV//.
move: (qb i j   (J (Vg (P t) j) (Vg (Q t) j)) lij); rewrite LgV// => hh.
have ww: inc (J (Vg (P t) j) (Vg (Q t) j))
   (source (Vg (psf S) (J i j)) \times source (Vg (psf S') (J i j))).
  rewrite /ext_to_prod; aw; rewrite sij sij'.
  apply:setXp_i; aw.
  - by apply:pv.
  - by apply:qv; rewrite - (prl_same_index_same_I same_I).
have qq: inc (J (Vg (P t) j) (Vg (Q t) j)) (graph (Vg u j)).
  move:(hu3 _ jI) => [fu su tu].
  rewrite xv  - prl_map_val_aux2//; apply: (Vf_pr3 fu); rewrite su.
  by apply: pv.
rewrite (hh qq) s_f' /prl_product_f (LgV lij)(ext_to_prod_V2 fij fij' ww).
by rewrite  pr1_pair pr2_pair -(pw _ _ lij) - (qw _ _ lij').
Qed.

Lemma  ex3_gl_val_bf (E := (projective_limit ex3limit_graphs))
       (f:= Lf ex3_gl_val ex3_graphs_limit  E):
  bijection_prop f ex3_graphs_limit E.
Proof.
have ax:= ex3_gl_val_ax.
rewrite /f;saw.
case:(prl_map2_prop same_I Hu); set fp := (projective_limit_fun S S' u).
  move => [fff sff tff] ffp.
have huu i: inc i (psI S) ->
              function_prop (Vg u i) (Vg (psE S) i) (Vg (psE S') i). 
   by move => iI; move:Hu => [_ _ h _]; move: (h _ iI). 
have hu i: inc i (psI S) -> function (Vg u i) by case /huu.
apply: (lf_bijective ax).
  move => u1 u2 u1g u2g sv.
  rewrite (in_graph_Vf fff u1g) (in_graph_Vf fff u2g).
  suff : (P u1) =  P u2 by move ->.
  move: (p1graph_source1 fff u1g) (p1graph_source1 fff u2g). 
  rewrite sff.
  move => /prl_limitP [pu1g u1d u1v u1w].
  move => /prl_limitP [pu2g u2d u2v u2w].
  apply: fgraph_exten => //; first by rewrite u1d u2d.
  rewrite u1d  => i iI.
  move: (f_equal (fun z => P (Vg z i)) sv);rewrite /ex3_gl_val.
  by rewrite !LgV//; aw.
move => y yp. 
move:(prl_subsets_prop ex3_prl_subfm_hyp).
rewrite -/ex3limit_graphs; move => [s_E s_I s_r s_f].
move:(yp) =>/prl_limitP[yg yd yv yw].
set x1 := (Lg (psI S) (fun i => (P (Vg y i)))).
set x2 := (Lg (psI S) (fun i => (Q (Vg y i)))).
have dy: domain (psE ex3limit_graphs) = psI S by rewrite s_E Lgd.
rewrite s_E in yv.
have xyv : y = ex3_gl_val (J x1 x2).
  rewrite /ex3_gl_val; apply:fgraph_exten; aww.
  rewrite /x1 /x2 yd => i iI; rewrite  ! LgV//; aw.
  move:(hu _ iI) => fu.
  by move: (yv _ iI); rewrite LgV//  => yig;rewrite (function_sgraph fu yig).
have xsp: inc x1 (projective_limit S).
  apply/Zo_P; split.
    rewrite /x1; apply/setXb_P; rewrite ps_domain_E; split; aww. 
    move => i iI; rewrite LgV//; move:(yv _ iI)(huu _ iI); rewrite LgV// => yv' [fu <- _].
    exact: (p1graph_source1 fu yv').
  move => i j lij.
  move:(prl_system_product_prop same_I) =>[s_E' s_I' s_r' s_f'].
  move: (prl_prop0 lij) => [iI jI].
  move:(ps_function_f lij) => [fij sij _].
  move:(lij); rewrite same_I => lij'.
  move:(ps_function_f lij') => [fij' sij' _].
  move:(yv _ iI)(yv _ jI);rewrite /x1 !LgV// => yv1 yv2.
  move: (prl_subfam_prop1 ex3_prl_subfm_hyp) (yw _ _ lij)=> [_ Fb _ _ _].
  move: (Fb _ _ (Vg y j) lij); rewrite  LgV// => ww; move: (ww  yv2)=> {Fb ww}.
  move => -> -> /=; rewrite  /prl_product_f (LgV lij).
  rewrite (ext_to_prod_V2 fij fij') ?pr1_pair // sij sij'; aw.
  move: (huu _ jI) => [fuj <- <-].
  rewrite - (function_sgraph fuj yv2);  apply:setXp_i.
  - exact:(p1graph_source1 fuj yv2).
  - exact:(p2graph_target1 fuj yv2).
move:(xsp); rewrite - sff => xsp'.
have pqx: x2 = Vf fp x1.
  move:(Vf_target fff xsp'); rewrite  tff => /prl_limitP[vg vd vv vw].
  rewrite /x2; apply: fgraph_exten => //; aww.
    by rewrite vd (prl_same_index_same_I same_I).
  move => i iI /=. 
  rewrite -(prl_map_val_aux2 same_I Hu iI xsp) /x1 LgV//.
  by move:(yv _ iI) (hu _ iI); rewrite ! LgV// => yv' fu; apply: Vf_pr2.
by exists (J x1 x2) => //; rewrite pqx;apply:(Vf_pr3 fff xsp').
Qed.

  
End Exercise3.


(* Noter *)
Lemma cpred_double n: natp n -> cpred (cpred (cdouble n)) = cdouble (cpred n).
Proof.
move => nN; case: (equal_or_not n \0c) => nz.
  by rewrite nz /cdouble cpred0 cprod0r !cpred0.
move: (cpred_pr nN nz) => [sa {1} ->]; rewrite (double_succ sa).
move: (NS_double sa) => sb; move:(NS_succ sb)=> sc.
rewrite !cpred_pr2 //.
Qed.


(** Exercise 4 *)

Definition ex4_prop_IR I r:= 
  [/\ nonempty I, order r,substrate r = I, right_directed r &
   forall x, inc x I -> ~(greatest r x)].


Definition ex4d_orderI A := Zo (\Po A) finite_set.
Definition ex4d_orderr A := sub_order (ex4d_orderI A).

Lemma ex4d_orderIr_prop1 A: infinite_set A ->
       ex4_prop_IR  (ex4d_orderI A)(ex4d_orderr A).
Proof.
move => h.
move: (finite_subsets_order A) => [qa qb qc qd qe].
move: (qa) => [pa pb].
split => //.
- exists emptyset;apply/Zo_P; split; [ apply:setP_0i| apply: emptyset_finite].
- rewrite /greatest pb;move => x xI [_ xg].
  have: ssub x A.
    move/Zo_P: xI => [/setP_P xA xf]; split => // exa.
    by case: (proj2 xf); rewrite exa.
  move/setC_ne=> [y /setC_P [yA]]; case.
  move: (xg _ (qb _ _ xI (qd _ yA))) => /sub_gleP [_ _]; apply; fprops.
Qed.

Definition uncountable_set x := ~ (countable_set x).

Lemma uncountable_set_infinite x: uncountable_set x -> infinite_set x.
Proof.
by move => h; case: (finite_or_infinite_set x) => // /finite_is_countable.  Qed.

Lemma ex4d_orderIr_prop2 A z: uncountable_set A ->
  cofinal (ex4d_orderr A) z -> countable_set z -> False.
Proof.
move => ha [hb hc] hd.
move: (finite_subsets_order A);set I := Zo (\Po A) finite_set.
move =>[[or sr] pb pc pd pe].
rewrite sr in hc hb.
set f := (identity_g z).
have df : domain f = z by rewrite /f identity_d.
have he: (countable_set (domain f)) by rewrite df.
have hf: allf f countable_set.
  move => x; rewrite df => xz; rewrite/f (identity_ev xz).
  by move:(hb _ xz) => /Zo_P[_ /finite_is_countable].
move:(countable_union he hf); rewrite setUb_identity.
have -> // : union z = A.
set_extens t.
  by move/setU_P =>[y ty yz]; move:(hb _ yz)=> /Zo_P [/setP_P yA _];apply: yA.
move => tA; move:(hc _ (pd _ tA)) => [y yz /sub_gleP[_ _ ty]].
apply/setU_P; ex_tac.
Qed.

  
Lemma ex4d_orderIr_prop3 (A:= \Po Nat):
  ex4_prop_IR (ex4d_orderI A)(ex4d_orderr A) /\
  forall z, cofinal (ex4d_orderr A) z -> ~ countable_set z.
Proof.
move: (card_setP Nat) cardinal_Nat ; rewrite -/A => cA cN.
have ccN: cardinalp Nat by rewrite - cN; fprops.
have ucA: uncountable_set A.
  by move/countableP => /cleNgt []; move:(cantor ccN); rewrite - cA.
split; first by apply:(ex4d_orderIr_prop1 (uncountable_set_infinite ucA)).
move => z zcf zco; exact:(ex4d_orderIr_prop2 ucA zcf zco).
Qed.
  
Section Exercise4.
Variable I r: Set.

Hypothesis ex4H:ex4_prop_IR I r.

Lemma ex4_no_greater x: inc x I -> exists y, glt r x y.
Proof.
move => xI.
move: ex4H => [neI or sr rdr noge].
move/right_directedP: rdr => [_];rewrite / right_directed_prop sr => h.
case: (p_or_not_p (exists2 y, inc y I & ~(gle r y x))).
  move => [y yI nxy]; move:(h _ _ xI yI) =>[z [ qa qb]].
  by exists z; split => // exz; case: nxy; rewrite exz.
move => dy;case (noge _ xI); rewrite /greatest sr;  split => // y yI.
by ex_middle bad; case dy; exists y.
Qed.


Lemma ex4_or_prop0 i j: gle r i j -> inc i I /\ inc j I.
Proof.
by move: ex4H => [_ _ <- _ _] lij; move: (arg1_sr lij)(arg2_sr lij).
Qed.  

Lemma ex4_or_prop1: exists x y, glt r x y.
Proof. 
by move:ex4H => [[x xI] _ _ _ _];move:(ex4_no_greater xI) => [y yp]; exists x,y.
Qed.

Definition ex4_seq_prop1 s n:=
  forall i, i <c n -> glt r (P (Vg s i)) (Q (Vg s i)).
Definition ex4_seq_prop2 s n:=
  forall i j, j <c i -> i <c n -> ~(gle r (P (Vg s i)) (P (Vg s j))).

Definition ex4_seqp s n :=
  [/\ natp n, fgraph s, domain s = n, 
      ex4_seq_prop1 s n & ex4_seq_prop2 s n].

Definition ex4_F :=
  Zo (sub_fgraphs Nat (coarse I)) (fun z => exists2 n, n <> \0c & ex4_seqp z n).

Definition ex4_last x := cpred (domain x).
Definition ex4_fct_r x := P (Vg x (ex4_last x)).
Definition ex4_fct_s x := Q (Vg x (ex4_last x)).

Lemma ex4_inF_hi x (n := domain x): inc x ex4_F ->
  [/\ n <> \0c, ex4_seqp x n  & forall i, i<c n -> pairp (Vg x i)].
Proof.
move/Zo_P => [ha  [m mp hu]]; move: (hu)=> [hb hc hd _ _].
move/sub_fgraphsP: (ha) => [C CN /gfunctions_P2 [_ _ xr]].
rewrite /n  hd; split => // i /(NltP hb) lim.
have: inc (Vg x i) (range x) by apply/(range_gP hc); exists i => //; ue.
by move/xr => /setX_P [].
Qed.

Lemma ex4_length_prop1 x (n := ex4_last x):  inc x ex4_F ->
  natp n /\ domain x = csucc n.
Proof.
move => / ex4_inF_hi [mz [ra _ _ _ _ _]]; exact:(cpred_pr ra mz).
Qed.

Lemma ex4_inF x n : n <> \0c -> ex4_seqp x n ->
  (forall i, i<c n -> pairp (Vg x i)) ->
  inc x ex4_F.
Proof.
move => ha hb hc.
move: (hb)=> [q1 q2 q3 q4 q5]; apply/Zo_P; split => //; last by exists n.
apply/sub_fgraphsP; exists n;first by move => t tn; move:(NS_inc_nat q1 tn).
apply/gfunctions_P2; split => // t /(range_gP q2) [j jdx ->].
move: jdx; rewrite q3 => /(NltP q1) => ljn.
move:(proj1(q4  _ ljn)) => lij; move:(ex4_or_prop0 lij) => [p1 p2].
by move:(hc _ ljn) =>p3;apply/setX_P.
Qed.
  
Lemma ex4_fct_r_in_I x: inc x ex4_F ->
 [/\ inc (ex4_fct_r x) I, inc (ex4_fct_s x) I &
     glt r (ex4_fct_r x) (ex4_fct_s x)].
Proof.
move => hx; move:(ex4_length_prop1 hx) => [sa sb].
move:(ex4_inF_hi hx) => [p1 [pa pb pc pd pe] p2].
have qq:ex4_last x <c domain x by rewrite sb; apply:cltS.
by move: (pd _ qq) => lt; move:(ex4_or_prop0 (proj1 lt)) => [iI jI].
Qed.


Lemma ex4_F_special i: inc i I -> exists2 x, inc x ex4_F & ex4_fct_r x = i.
Proof.
move => iI.
move:(ex4_no_greater iI) => [j lij].
set x := Lg \1c (fun z => J i j).
have fgx: fgraph x by rewrite /x; fprops.
have dx: domain x = \1c by rewrite /x; aw.
have ha: ex4_fct_r x = i.
  by rewrite/ex4_fct_r /ex4_last dx cpred1 /x LgV//; aw;trivial;apply:set1_1.
have hb:forall k, k <c \1c -> pairp (Vg x k).
  rewrite /x;  move=> k /(NltP NS1) kk; rewrite  LgV//; fprops.
exists x => //;apply:(ex4_inF card1_nz _ hb); split; fprops.
  by rewrite /x;move => t /(NltP NS1) kk; rewrite LgV//;aw.
by move => a b lab /clt1 bz; move: lab; rewrite bz => /clt0.
Qed.

Lemma ex4_F_nonempty: nonempty ex4_F.
Proof.
move: ex4H => [[i iI] _ _ _ _]; move:(ex4_F_special iI) => [x xF _]; ex_tac.
Qed.

Definition ex4_setEi i := Zo ex4_F (fun z => ex4_fct_r z =  i).

Lemma ex4_setEi_nonempty i: inc i I -> nonempty(ex4_setEi i).
Proof. by move/ex4_F_special => [x xa xb]; exists x; apply/Zo_P. Qed.

Lemma ex4_F_stable_restr x m: inc x ex4_F -> m <=c domain x -> m <> \0c ->
  inc (restr x m) ex4_F.
Proof.
move/ex4_inF_hi => [h1 [h2 h3 _ h5 h6 ] h7] pa pb.
have mN := NS_le_nat pa h2.
have ra i: i <c m -> (Vg (restr x m) i) = Vg x i.
  by move => lim;rewrite LgV//; apply/(NltP mN). 
have rb i: i <c m -> pairp (Vg (restr x m) i).
  move => lim; rewrite (ra _ lim); apply: (h7 _ (clt_leT lim pa)).
apply:(ex4_inF pb _ rb); split => //. 
- fprops.
- by aw.
- move => i lim; rewrite (ra _ lim); apply: (h5 _ (clt_leT lim pa)).
- move => i j lji lim; rewrite (ra _ lim) (ra _ (clt_ltT lji lim)).
  apply:(h6 _ _ lji  (clt_leT lim pa)).
Qed.

Definition ex4_modify_r x i:=
  Lg (domain x) (fun z => Yo (z = ex4_last x) (J i (Q (Vg x z))) (Vg x z)).

Lemma ex4_F_stable_modify_r x i:
  inc x ex4_F -> gle r i (ex4_fct_r x) ->
  (forall k,  k <c (ex4_last x) -> ~ gle r i (P (Vg x k))) ->
  inc (ex4_modify_r x i) ex4_F.
Proof.
move => hx;move:(ex4_length_prop1 hx) => [sa sb].
move /ex4_inF_hi:hx => [h1 [h2 h3 _ h5 h6 ] h7] pa pc.
set y := ex4_modify_r x i.
have qq:ex4_last x <c domain x by rewrite sb; apply:cltS.
have fgy: fgraph y by rewrite/y/ex4_modify_r; fprops.
have dy: domain y = domain x by rewrite/y/ex4_modify_r; aw.
have yl: Vg y (ex4_last x) =  (J i (Q (Vg x (ex4_last x)))).
  by rewrite /y /ex4_modify_r; rewrite LgV//; [ Ytac0 | apply/(NltP h2) ].
have ynl j:j <c (domain x) -> j <>  (ex4_last x) -> (Vg y j) = (Vg x j).
  by move =>  /(NltP h2)ha hb; rewrite/y /ex4_modify_r; rewrite LgV//; Ytac0.
have qa j:  j <c domain x -> pairp (Vg y j).
  move =>  jd; case: (equal_or_not j (ex4_last x)) => jl.
      rewrite jl yl; fprops.
    by rewrite ynl //;  apply:h7.
have or: order r by move:ex4H => [].
apply:(ex4_inF h1 _ qa); split => //.
  move => j lij; move:(h5 _ lij) => ih5.
  case: (equal_or_not j (ex4_last x)) => jl; last by rewrite ynl.
  by rewrite jl yl; aw; apply: (leq_lt_trans or pa); rewrite/ex4_fct_r - jl.
move => j k lkj ljm.
have ljm': j <=c (ex4_last x) by apply/(cltSleP sa); rewrite - sb.
rewrite (ynl _ (clt_ltT lkj ljm) (proj2 (clt_leT lkj ljm'))).
case: (equal_or_not j (ex4_last x)) => jl.
  by rewrite jl yl; aw; apply: (pc k); rewrite - jl. 
by rewrite (ynl _ ljm jl); apply: h6.
Qed.

Lemma ex4_modify_r_r x i:
  inc x ex4_F -> ex4_fct_r (ex4_modify_r x i)  = i.
Proof.
move => ha; move:(ex4_length_prop1 ha).
rewrite /ex4_modify_r/ex4_fct_r /ex4_last; move => [sa sb].
rewrite Lgd LgV//; first by  Ytac0; aw.
rewrite {2} sb; apply/(NltP (NS_succ sa)); apply:(cltS sa).
Qed.
  
  
Definition ex4_indexj x a:=
  intersection (Zo (domain x) (fun j => gle r a (P (Vg x j)))).

Lemma ex4_indexj_correct x a (j := ex4_indexj x a):
  inc x ex4_F -> gle r a (ex4_fct_r x) ->
  [/\ j <c (domain x),  gle r a (P (Vg x j)) &
      forall k, k <c (domain x) ->  gle r a (P (Vg x k)) -> j <=c k].
Proof.
move => ha hb.
rewrite /j /ex4_indexj; set U := Zo _ _.
move: (ex4_length_prop1 ha); set n := domain x; move => [xa xb].
have nN: natp n by rewrite xb; apply: NS_succ.
have csu: cardinal_set U.
  move => t /Zo_P [ h _]; exact:(CS_nat (NS_inc_nat nN h)).
have neu: nonempty U.
  exists (cpred n); apply /Zo_P; split => //. 
    by apply/(NltP nN); rewrite {2} xb; apply: (cltS xa).
move: (cle_wor' csu neu); set u := intersection U; move => [ua ub].
move/Zo_P: ua => [ /(NltP nN) ra rb];  split => // k lkn h.
by apply: ub; apply/Zo_P; split => //; apply/(NltP nN).
Qed.


Lemma ex4_indexj_idem x:inc x ex4_F -> ex4_indexj x (ex4_fct_r x) = ex4_last x.
Proof.
move => ha.
move:(ex4_fct_r_in_I ha); set i:= (ex4_fct_r x); move => [iI _ _].
have leii: gle r i i by move:ex4H => [_ or sr  _ _ ]; order_tac; rewrite sr.
move:(ex4_indexj_correct ha leii) => [p1 p2 p3].
move: (ex4_length_prop1 ha) => [nN nv].
move /ex4_inF_hi: ha => [sa [q1 _ _ _ q5] _ ].
have la: (ex4_last x) <c domain x by apply: cpred_lt.
move: p1; rewrite {1} nv; move/(cltSleP nN); case/cle_eqVlt => // lt.
by case: (q5  _ _ lt la).
Qed.

Definition ex4_function_fv a x :=
  ex4_modify_r (restr x (csucc (ex4_indexj x a))) a.


Lemma  ex4_function_f_prop1 x a (y := ex4_function_fv a x):
  inc x ex4_F -> gle r a (ex4_fct_r x) ->
  inc y ex4_F /\  (ex4_fct_r y)  = a.
Proof.
move => ha hb.
move /ex4_inF_hi:(ha) => [h1 [h2 _ _ h5 h6 ] _].
move: (ex4_indexj_correct ha hb).
set j:= (ex4_indexj x a); move => [ja jb jc].
set y1 :=  (restr x (csucc (ex4_indexj x a))).
move: (NS_lt_nat ja h2) => jN.
have lt1:csucc j <=c domain x by apply/(cleSltP jN).
have pa: inc y1 ex4_F by apply:(ex4_F_stable_restr ha lt1); apply:succ_nz.
have pb: ex4_fct_r y = a by rewrite/y -/y1; apply: ex4_modify_r_r.
have pc: ex4_last y1  = j by rewrite /y1/ex4_last restr_d (cpred_pr2 jN).
have pd: gle r a (ex4_fct_r y1).
   rewrite /ex4_fct_r pc /y1 -/j; rewrite LgV//;  apply/(NltP (NS_succ jN)); fprops.
split => //; apply:(ex4_F_stable_modify_r pa pd).
rewrite pc => k lkj; rewrite /y1 -/j.
have lkj': inc k (csucc j).
  by apply/(NltP (NS_succ jN)); move: (clt_leT lkj (cleS jN)).
by rewrite LgV//; move => h; case:(cleNgt(jc _ (clt_ltT lkj ja) h)).
Qed.

Lemma ex4_function_f_ax a b: gle r a b ->
  lf_axiom (ex4_function_fv a)  (ex4_setEi b) (ex4_setEi a).
Proof.
move=> lab x /Zo_P[xF rx]; rewrite - rx in lab.
by move:(ex4_function_f_prop1 xF lab) => h; apply/Zo_P.
Qed.  

Definition ex4_function_f ab :=
  Lf (ex4_function_fv (P ab)) (ex4_setEi (Q ab))   (ex4_setEi (P ab)). 
Definition ex4_function_f_fam := Lg r  ex4_function_f.

Lemma ex4_function_f_fun a b: gle r a b ->
  function_prop (ex4_function_f (J a b)) (ex4_setEi b)  (ex4_setEi a).
Proof.
rewrite /ex4_function_f;move => lab; saw; apply: lf_function.
by move => x; apply: ex4_function_f_ax.
Qed.

Lemma ex4_function_f_id a: inc a I ->
  (ex4_function_f (J a a)) = identity (ex4_setEi a).
Proof.
move => aI.
move:(ex4H) => [_ or sr  _ _].
have leaa: gle r a a by order_tac; rewrite  sr.
move:(ex4_function_f_fun leaa) (ex4_function_f_ax leaa) => [pa  pb pc] ax.
apply: function_exten; aww; rewrite pb => x  xp.
rewrite /ex4_function_f (idV xp); aw; rewrite LfV//.
rewrite / ex4_function_fv. 
move/Zo_P: xp => [xf xv].
move: (ex4_length_prop1 xf) => [nN nv].
move: (ex4_indexj_idem xf); rewrite xv => eq; rewrite eq - nv /restr.
move:(ex4_inF_hi xf) => [_[h1 h2 _ _ _ ]] h3.
rewrite (Lg_recovers h2) / ex4_modify_r; apply:fgraph_exten; aww.
move => i idx /=; rewrite LgV//; Ytac eq1 => //; rewrite - xv.
by rewrite /ex4_fct_r - eq1 h3 //; apply/(NltP h1).
Qed.

Lemma ex4_compose_f i j k (psf :=  ex4_function_f_fam):
  gle r i j -> gle r j k ->
  Vg psf (J i j) \co  Vg psf (J j k) = Vg psf (J i k).
Proof.
move => lij ljk.
move:(ex4H) => [_ or sr  _ _].
have lik: gle r i k by order_tac.
rewrite /psf /ex4_function_f_fam LgV//.
move:(ex4_function_f_fun lij) => [fij sij tij].
move:(ex4_function_f_fun lik) => [fik sik tik].
move:(ex4_function_f_fun ljk) => [fjk sjk tjk].
move:(ex4_function_f_ax lij) =>  axij.
move:(ex4_function_f_ax lik) =>  axik.
move:(ex4_function_f_ax ljk) => axjk.
have co: ex4_function_f (J i j) \coP ex4_function_f (J j k).
  split; fprops; ue.
rewrite !LgV //;apply:function_exten;aw; trivial; try ue; first by fct_tac; ue.
rewrite sjk => x xv; rewrite compfV//; try ue.  
rewrite /ex4_function_f; aw.
rewrite (LfV axik xv) (LfV axjk xv) (LfV axij (axjk _ xv)).
clear fij sij tij fik sik tjk fjk sjk tik axij axik axjk co.
move/Zo_P: xv => [xF rx]; rewrite - rx in ljk lik.
move:(ex4_function_f_prop1 xF ljk) => [y3F y3r].
have lij':  gle r i (ex4_fct_r (ex4_function_fv j x)) by rewrite y3r.
set y3 :=  (ex4_function_fv j x).

rewrite /ex4_function_fv.
set i1 := (ex4_indexj x i).
set i2 := (ex4_indexj x j).
set y1 := (restr x (csucc i1)).
set y2 := (restr x (csucc i2)).
move: (ex4_indexj_correct y3F lij').
move: (ex4_indexj_correct xF ljk).
move: (ex4_indexj_correct xF lik).
rewrite -/i1 -/i2; move =>[i1p1 i1p2 i1p3] [i2p1 i2p2 i2p3].
rewrite -/y3; set i3 := ex4_indexj y3 i;move =>  [i3p1 i3p2 i3p3].
move:(or) => [_ _ ot _].
have li1i2: i1 <=c i2 by apply: (i1p3 _ i2p1); apply:(ot _ _ _ lij i2p2).
have dy3: domain y3 = csucc i2.
  by rewrite /y3 /ex4_function_fv /ex4_modify_r; aw.
rewrite dy3 in i3p1 i3p3.
have nN: (natp (domain x)) by move/ex4_inF_hi:xF => [_ []].
have i1N := NS_lt_nat i1p1 nN.
have i2N := NS_lt_nat i2p1 nN.
have lei3i2: i3 <=c i2 by apply/(cltSleP i2N).
have i3N := NS_le_nat lei3i2 i2N.
have lt0: i1 <c csucc i2  by apply/(cltSleP i2N).
have lt1: inc i1 (csucc i2) by apply /(NltP (NS_succ i2N)). 
have lei3i1: i3 <=c i1.
  apply: (i3p3 _ lt0).
  rewrite /y3 /ex4_function_fv /ex4_modify_r -/i2/ex4_last; aw.
  rewrite  (LgV lt1) LgV// (cpred_pr2  i2N). Ytac eq1; aw; trivial.
have lt2: inc i3 (csucc i2) by apply /(NltP (NS_succ i2N)). 
have lei1i3: i1 <=c i3.
  case: (equal_or_not i3 i2) => eqa; first by rewrite eqa.
  apply: (i1p3 _  (cle_ltT lei3i2 i2p1)).
  move: i3p2; rewrite /y3 /ex4_function_fv /ex4_modify_r -/i2/ex4_last.
  by aw;rewrite ! LgV// (cpred_pr2 i2N); Ytac0.
have ei1i3: i1 = i3 by apply:cleA.
have dy1: domain y1 = csucc i1 by rewrite /y1 restr_d.
rewrite /ex4_modify_r; apply: fgraph_exten; try apply: Lg_fgraph.
  by rewrite 2!Lgd dy1 restr_d ei1i3.
rewrite Lgd restr_d dy1 - ei1i3 => t ts3; rewrite LgV//.
have lt3: t <=c i1 by apply/(cltSleP i1N); apply/(NltP (NS_succ i1N)).
have lt4: inc t (csucc i2).
   apply/(NltP (NS_succ i2N)); apply/(cltSleP i2N); apply: (cleT lt3 li1i2).
rewrite /ex4_last restr_d dy1 (cpred_pr2 i1N); rewrite LgV // LgV//.
rewrite /y3 /ex4_function_fv /ex4_modify_r restr_d - /i2 (LgV lt4).
rewrite (restr_ev _ lt4) /ex4_last restr_d (cpred_pr2 i2N) /y1 (restr_ev _ ts3).
Ytac eqa; Ytac0; Ytac eqc => //; aw; trivial.
by case:(cleNgt (li1i2)); rewrite - eqc.
Qed.

Lemma ex4_function_f_sf a b:gle r a b ->
  surjection (ex4_function_f (J a b)). 
Proof.
move => leab.
move:ex4H  => [_ or sr _ _].
move: (arg1_sr leab) (arg2_sr leab); rewrite sr => aI bI.
case: (equal_or_not a b) => eqab.
   by rewrite eqab (ex4_function_f_id bI); case: (identity_fb (ex4_setEi b)).
apply: lf_surjective; first by apply: ex4_function_f_ax; aw.
aw; move => y /Zo_P [yF yr].
move:(ex4_length_prop1 yF) => [sa sb].
move/ex4_inF_hi:yF =>[y1 [nN y3 y4 y5 y6] y7].
set n := domain y.
move:(ex4_no_greater bI) => [c cI].
pose x := Lg (csucc n) (fun z => Yo (z <c n) (Vg y z) (J b c)).
have dx: domain x = csucc n by rewrite /x Lgd.
have lenn:= (cleS nN).
have snN:= (NS_succ nN).
have xv_in i: i <c n -> Vg x i = Vg y i.
  move => iN; rewrite /x LgV//; first by Ytac0.
  apply/(NltP snN); apply: (clt_leT iN lenn).
have xv_out:  Vg x n = (J b c).
   rewrite/x LgV//; first by rewrite Y_false //; case.
    apply/(NltP snN); exact:(cltS nN).
have fgx: fgraph x by rewrite /x; fprops.
have hu: ex4_last y <c n by rewrite /n sb; apply:cltS.
have dxnz:= (@succ_nz n).
have xF: inc x (ex4_F). 
  have pa i: i <c csucc n -> pairp (Vg x i).
    move/(cltSleP nN);case/cle_eqVlt => lt;first by rewrite lt xv_out; fprops.
    by rewrite (xv_in _ lt); apply: y7.
  apply/(ex4_inF dxnz _ pa); split => //. 
    move => i/(cltSleP nN);case/cle_eqVlt => lt; first by rewrite lt xv_out; aw.
    by rewrite (xv_in _ lt); apply: y5.
  move => i j lji /(cltSleP nN) lein.
  rewrite (xv_in _ (clt_leT lji lein)); case/cle_eqVlt:lein => lt; last first.
    by rewrite (xv_in _ lt); apply: y6.
  rewrite lt xv_out pr1_pair  => lebv.
  have ltab: glt r a b by split.
  have laij: glt r a (P (Vg y j)) by order_tac.
  case: (equal_or_not j (ex4_last y)) => jv.
    by case: (proj2 laij); rewrite - yr jv.
  have hv: j <c ex4_last y by split=> //;apply/(cltSleP sa); rewrite - sb -lt.
  move:(y6 (ex4_last y) j hv hu); case; rewrite -/(ex4_fct_r y) yr. 
  exact: proj1 laij.
have xr: ex4_fct_r x = b.
  by rewrite /ex4_fct_r {2}/x /ex4_last Lgd (cpred_pr2 nN) xv_out; aw.
have xe: inc x (ex4_setEi b) by apply /Zo_P.
exists x => //.
have leaxv: gle r a (ex4_fct_r x) by rewrite xr.
case:(ex4_indexj_correct xF leaxv).
set d := ex4_indexj x a; rewrite dx; move/(cltSleP nN) => dp1 dp2 dp3.
have ha: (ex4_last y) <c csucc n by apply: (clt_leT hu (cleS nN)).
case: (NleT_ell (NS_le_nat dp1 nN) sa); last first.
    case/cltNge; apply:(dp3 _ ha). 
    by rewrite (xv_in _ hu) -/(ex4_fct_r y) yr;  order_tac; rewrite sr.
  move => lt1.
  case: (y6 (ex4_last y) d lt1 hu); rewrite -/(ex4_fct_r y) yr - (xv_in) //.
  apply: (clt_ltT lt1 hu).
move => dv.
rewrite /ex4_function_fv -/d dv - sb /ex4_modify_r  /ex4_last restr_d.
apply: fgraph_exten;[done | fprops| by aw | move => i idg /=; rewrite LgV //LgV//].
move/(NltP nN): idg => lin.
rewrite (xv_in _ lin); Ytac eqa => //.
by rewrite - yr /ex4_fct_r /ex4_last - eqa y7.
Qed.

Definition ex4_system: projective_system.
Proof.
move:(ex4H) => [_  or sr _ _].
apply:(@ProjectiveSystem (Lg I ex4_setEi) I r ex4_function_f_fam). 
- by move/order_preorder:or.
- exact.
- fprops.
- by aw.
- rewrite /ex4_function_f_fam; fprops.
- by rewrite /ex4_function_f_fam Lgd.
- move => i ir.
  move:(pr1_sr ir)(pr2_sr ir); rewrite sr => iI jI.
  move: (order_sgraph or ir) => pi; move: ir;rewrite - {1 2} pi => pir.
  rewrite LgV // /ex4_function_f_fam !LgV//; exact:(ex4_function_f_fun pir). 
- by move => i j k lij ljk;  apply: ex4_compose_f.
- move => i iI; rewrite /ex4_function_f_fam ! LgV//.
     by apply:ex4_function_f_id.
  by order_tac; rewrite sr.
Defined.

Lemma  ex4_system_prop: projective_system_on ex4_system
   (Lg I ex4_setEi) I r ex4_function_f_fam.
Proof.  by rewrite /ex4_system; case: ex4H => [pa pb pc pd pe]. Qed.

Lemma ex4_propb a b c x y z: gle r a c -> gle r b c -> inc z (ex4_setEi c) ->
  x = Vf (ex4_function_f (J a c)) z -> y = Vf (ex4_function_f (J b c)) z  ->
  domain x = domain y ->
  ex4_fct_s x = ex4_fct_s y.
Proof.
move => leac lebc zf.
move: (ex4_function_f_ax leac) (ex4_function_f_ax lebc) => ax1 ax2.
rewrite /ex4_function_f; aw; rewrite !LfV// => -> ->.
rewrite /ex4_function_fv /ex4_modify_r 2!Lgd 2!restr_d.
set m := csucc (ex4_indexj z a) => mv; rewrite - mv.
rewrite /ex4_fct_s /ex4_last 2!Lgd restr_d.
move/Zo_P:(zf) => [zE zr]; rewrite - zr in leac.
move:(proj31 (ex4_indexj_correct zE leac)) => lab.
move/ex4_inF_hi: zE => [_ [ dN _ _ _ _] _].
have iN:= NS_lt_nat lab dN.
have ha: inc (cpred m) m.
  rewrite (cpred_pr2 iN); apply/(NltP (NS_succ iN))/(cltS iN).
by rewrite ! LgV //; Ytac0;Ytac0; aw.
Qed.

Lemma ex4_propc x (s := fun_image I (fun z => ex4_fct_s (Vg x z))):
  inc x  (projective_limit ex4_system) ->
  countable_set s /\ cofinal r s.
Proof.
move:ex4_system_prop =>[s_E s_I s_r s_f].
move => /prl_limitP; rewrite  s_I s_r s_E s_f ; move => [fgx dx xa xb].
have ha i: inc i I -> inc (Vg x i) (ex4_setEi i).
   move=> iI; move:(xa _ iI); rewrite LgV//.
pose rr i := ex4_fct_r (Vg x i).
pose ss i := ex4_fct_s (Vg x i).
have rri i: inc i I -> rr i = i by move => /ha /Zo_P[].
have hb i: inc i I ->  inc (ss i) I /\ glt r i (ss i).
  move => iI; move/Zo_P:(ha _ iI)=> [xf _].
  by case:(ex4_fct_r_in_I xf); rewrite -/(rr i) -/(ss i) (rri _ iI).
move:(ex4H) => [_  or sr rdr _].
have cf: cofinal r s. 
   split; first  by move => t /funI_P [i /hb [qa _] ->]; rewrite sr.
   rewrite sr => i iI; move:(hb _ iI) => [qa [qb _]]; exists (ss i) => //.
   by apply/funI_P; exists i.
split => //.
have hc i j: inc i I -> inc j I -> domain (Vg x i) = domain (Vg x j) -> 
   ss i = ss j.
   move/right_directedP: rdr => [_];rewrite /right_directed_prop sr => rdr'.
   move => iI jI sd.
   move:(rdr' _ _ iI jI) => [k [le1 le2]].
   move: (xb _ _ le1) (xb _ _ le2); rewrite /ex4_function_f_fam !LgV// => ea eb.
   move: (arg2_sr le1); rewrite sr => kI.
   exact: (ex4_propb le1 le2 (ha _ kI) ea eb sd).
pose f := Lg Nat (fun n => (Zo s (fun z => exists i, [/\ inc i I, z = ss i &
     domain (Vg x i) = n]))).                                                   
have <- : unionb f = s.
  rewrite /f;set_extens t.
    by  move/setUb_P; aw; move => [y yd]; rewrite LgV//; case/Zo_P.
  move => ts; apply/setUb_P; aw; move/funI_P:(ts) => [z zI zv].
  move:(ha _ zI) => /Zo_P[/ex4_inF_hi[_ [nd _ _ _ _] _] _].
  by exists (domain (Vg x z)) => //; rewrite LgV//; apply/Zo_P; split => //; exists z.
rewrite/f; apply: countable_union; first by aw; apply: countable_Nat.
rewrite /allf; aw => n nN; rewrite LgV//; set Sn := Zo  _ _; apply: finite_is_countable.
have: small_set Sn.
  move => i j /Zo_P [aS [u [uI -> da]]] /Zo_P [jS [v [vI -> db]]].
  by apply: (hc _ _ uI vI); rewrite db.
case/small_set_pr. move => ->; apply:emptyset_finite.
move => [t ->]; apply:set1_finite.
Qed.
  
Lemma ex4_propc1: nonempty (projective_limit ex4_system) ->
  exists2 s, countable_set s & cofinal r s.
Proof.
by move => [x /ex4_propc []]; set s:= fun_image _ _ => ha hb; exists s.
Qed.  

End Exercise4.

Lemma ex4d (S:= (ex4_system (proj1 ex4d_orderIr_prop3))):
  [/\ (forall i, inc i (psI S) -> nonempty (Vg (psE S) i)),
      (forall ij, inc ij (psr S) -> surjection (Vg (psf S) ij)) &
      (projective_limit S) = emptyset].
Proof.
case:(ex4_system_prop (proj1 ex4d_orderIr_prop3)).
set Hu := (proj1 ex4d_orderIr_prop3).
rewrite -/S; move => s_E s_I s_r s_f.
rewrite  s_I s_r s_E s_f; split => //.
- by move => i iI; rewrite LgV//; apply:ex4_setEi_nonempty.
- move => ij ijr; rewrite/ex4_function_f_fam LgV//.
  have pp: pairp ij by move: (Hu) => [_ /order_sgraph sg _ _ _ ]; apply: sg.
  rewrite - pp in ijr |- *.
  exact:(ex4_function_f_sf Hu ijr).
- case: (emptyset_dichot (projective_limit S)) => // le.
  move:(ex4_propc1 le) => [s sa sb].
  case: (proj2 ex4d_orderIr_prop3 _ sb sa).
Qed.

Lemma ex4e (S := (ex4_system (proj1 ex4d_orderIr_prop3)))
      (S' := (prl_exa2_system \1c (ps_preorder_r S) (ps_substrate_r S)))
      (u:= (Lg (psI S) (fun z => (Lf (fun i => \0c) (Vg (psE S) z) \1c)))):
   [/\  prl_same_index S S',  prl_map2_compat S S' u,
  (forall i, inc i (psI S) -> surjection (Vg u i)) &
   ~(surjection (projective_limit_fun S S' u))].
Proof.
move: (ex4_system_prop (proj1 ex4d_orderIr_prop3)).
  rewrite -/S; move => [E_S I_S r_S f_S].
move:(prl_exa2_prop \1c (ps_preorder_r S) (ps_substrate_r S)).
  rewrite -/S'; move => [E_S' I_S' r_S' f_S'].
have pa: projective_limit S' = diagonal_graphp \1c (psI S).
  apply:prl_exa2_prop2; rewrite r_S.
  move:(proj1 ex4d_orderIr_prop3)=>[];set r:= ex4d_orderr (\Po Nat).
  move => _ _ sr rdr _ x y xsr ysr; move/right_directedP: rdr => [or h].
  rewrite - (ps_substrate_r S) r_S in xsr ysr.
  move: (h _ _ xsr ysr)=> [z [za zb]]; exists z; split => //.
  by move: (arg2_sr za); rewrite  -(ps_substrate_r S) r_S.
have [y ye]: nonempty (projective_limit S').
  rewrite pa; exists (cst_graph (psI S) \0c); apply/diagonal_graph_P.
   split; rewrite/constantgp; aw; trivial.
     by split; aww => i j iI jI;rewrite !LgV//.
   have ha: fgraph (cst_graph (psI S) \0c) by fprops.
   move => t /(range_gP ha); aw. trivial; move => [x xi ->]; rewrite LgV//; apply:set1_1.
have pc: prl_same_index S S' by [].
have pd: prl_map2_compat S S' u.
  rewrite /u; set W := (fun _ : Set => \0c).
  have ES' i: inc i (psI S)-> \1c = Vg (psE S') i by move=> iI;rewrite E_S' LgV.
  have hu i: inc i (psI S) ->  lf_axiom W (Vg (psE S) i) \1c.
    move => iI t tE; apply:set1_1.
  have hv i: inc i  (psI S) ->
     function_prop (Lf W (Vg (psE S) i) \1c) (Vg (psE S) i) (Vg (psE S') i).
     by move => iI; saw;[  apply:(lf_function (hu _ iI)) | apply: ES'].
  split; aww; first by move => i iI; rewrite LgV//; apply: hv.
  move => i j lij. 
  move:(arg1_sr lij) (arg2_sr lij); rewrite ps_substrate_r => iI jI.
  move: (ps_function_f lij); aw;move => [fij sij tij].
  move: (hv _ iI) (hv _ jI)=> [fi si ti][fj sj tj].
  have ha: Lf W (Vg (psE S) i) \1c \coP Vg (psf S) (J i j) by split => //; aw.
  have hb: Vg (psf S') (J i j) \coP Lf W (Vg (psE S) j) \1c. 
    by rewrite f_S' LgV //;split; fprops; aw.
  rewrite LgV //LgV//; apply: function_exten; aw; trivial.
  - by apply: compf_f. 
  - by apply: compf_f.
  - by rewrite f_S' LgV//; aw.
  - rewrite sij => t te.
    have ts: inc t (source (Vg (psf S) (J i j))) by ue.
    have tss:inc t (source (Lf W (Vg (psE S) j) \1c)) by aw.
    rewrite !compfV //  (LfV (hu _ jI)te).
    rewrite /W f_S' (LgV lij) (idV (set1_1 \0c)).  
    rewrite LfV//; fprops; Wtac. 
move:(proj1 (prl_map2_prop pc pd)); case; rewrite (proj33(ex4d)).
set v:= (projective_limit_fun S S' u) => [fv sv tv].
have nsv: ~ surjection v.
  by case;rewrite sv tv => _ h; move: (h _ ye) => [x /in_set0].
split => //  i iI.
rewrite /u LgV//; apply: lf_surjective; first by move => t _; apply: set1_1.
rewrite I_S in iI.
move:(ex4_setEi_nonempty (proj1 ex4d_orderIr_prop3) iI); rewrite {1} E_S.
by move => [k ke]  t/set1_P y0; exists k => //; rewrite LgV//.
Qed.


Section Exercise5.
  
Variable S: projective_system.
Variable Er Gf: Set.

Hypothesis rdr: right_directed_prop (psr S).
Hypothesis fgEr: fgraph Er.
Hypothesis dEr: domain Er = psI S.
Hypothesis lEr: forall i, inc i (psI S) -> lattice (Vg Er i).
Hypothesis sEr: forall i, inc i (psI S) -> substrate (Vg Er i) = Vg (psE S) i.
Hypothesis sen: forall i X, inc i (psI S) -> sub X (Vg (psE S) i) ->
   nonempty X -> exists a,  minimal (induced_order (Vg Er i) X) a.
Hypothesis fm: forall p, inc p (psr S) ->
     increasing_fun (Vg (psf S) p) (Vg Er (Q p))  (Vg Er (P p)).

Definition ex5_f i j := Vg (psf S) (J i j).

Hypothesis ex5_G1: fgraph Gf.
Hypothesis ex5_G2: domain Gf = psI S.
Hypothesis ex5_G3: forall i, inc i (psI S) -> nonempty (Vg Gf i).
Hypothesis ex5_G4: forall i, inc i (psI S) -> sub (Vg Gf i) (Vg (psE S) i).
Hypothesis ex5_G5: forall i x y,
    inc i (psI S) ->  inc x (Vg Gf i) -> inc y (Vg Gf i) -> x <> y ->
    ~ (ocomparable (Vg Er i) x y).
Hypothesis ex5_G6: forall i j, gle (psr S) i j ->
    Vfs (ex5_f i j) (Vg Gf j) = Vg Gf i.
Hypothesis ex5_G7:forall i j x, gle (psr S) i j ->  inc x (Vg Gf i) ->
  has_greatest (induced_order (Vg Er j) (Vfi1 (ex5_f i j) x)).
Hypothesis ex5_G8: forall i j h x,  gle (psr S) i j -> inc h (Vg (psE S) j) ->
   (exists2 y, inc y (Vg Gf j) & gle  (Vg Er j) y h) ->
   inc x (Vg Gf i)  -> gle (Vg Er i) x (Vf (ex5_f i j) h) ->
   exists x', [/\ inc x' (Vg Gf j),  gle  (Vg Er j) x' h & 
       x = Vf (ex5_f i j) x'].


Lemma ex5_Gsubfams: prl_subfam_hyp S Gf.
Proof. by split => // i j /ex5_G6 ->. Qed.

Definition ex5_S' :=projective_system_subsets (ex5_Gsubfams).


Definition ex5_X i j x := Vfi1 (ex5_f i j) x.
Definition ex5_M i j x :=
  the_greatest (induced_order (Vg Er j) (ex5_X i j x)).

Lemma ex5_Gij_prop1 i j x: gle (psr S) i j -> inc x (Vg Gf j) ->
  inc (Vf (ex5_f i j) x) (Vg Gf i).
Proof.
move => lij xj; rewrite -(ex5_G6 lij).
move:(prl_prop4 lij) => [fij sij tij].
move:(ex5_G4 (proj2 (prl_prop0 lij))); rewrite - sij => ss.
apply/(Vf_image_P fij ss); ex_tac.
Qed.

Lemma ex5_Gij_prop2 i j y: gle (psr S) i j -> inc y (Vg Gf i) ->
  exists2 x, inc x (Vg Gf j) & y =  Vf (ex5_f i j) x.
Proof.
move => lij; rewrite -(ex5_G6 lij) => yj.
move:(prl_prop4 lij) => [fij sij tij].
move:(ex5_G4 (proj2 (prl_prop0 lij))); rewrite - sij => ss.
by move/(Vf_image_P fij ss): yj.
Qed.

Lemma ex5_Xij_pr i j x: gle (psr S) i j -> 
   forall t, inc t (ex5_X i j x) <->
     (inc t (Vg (psE S) j) /\ x = Vf (ex5_f i j) t).
Proof.
by move/(prl_prop4) => [ff sf tf] t; move:(iim_fun_set1_P x ff t); rewrite sf.
Qed.


Lemma ex5_Xij_pr2 i j x:
  gle (psr S) i j -> sub (ex5_X i j x) (Vg (psE S) j).
Proof. by move => ha t; case/(ex5_Xij_pr x ha). Qed.

Lemma ex5_Mij_pr1 i j x (M:= ex5_M i j x):
  gle (psr S) i j ->  inc x (Vg Gf i) -> 
  inc M (ex5_X i j x) /\  
  forall t, inc t  (ex5_X i j x) -> gle (Vg Er j) t M.
Proof.
move => ha hb.
move:(prl_prop0 ha) => [iI jI].
move:(proj1 (lEr jI))(sEr jI) => or sr.
move:(ex5_Xij_pr2 ha (x:=x)); rewrite - sr => ss.
move: (iorder_osr or ss) => [or' sr'].
case:(the_greatest_pr or' (ex5_G7 ha hb)); rewrite iorder_sr //.
by move => ra rb; split => //; move => t/rb /iorder_gle1.
Qed.


Lemma ex5_Mij_pr2 i j x (M:= ex5_M i j x):
  gle (psr S) i j ->  inc x (Vg Gf i) -> 
  Vf (ex5_f i j) M = x /\  
  forall t, inc t (Vg (psE S) j) -> Vf (ex5_f i j) t = x -> gle (Vg Er j) t M.
Proof.
move => ha hb.
move:(ex5_Mij_pr1 ha hb) => [/(ex5_Xij_pr x ha) [hc1 hc2] hd].
by split => // t ta tb; apply: hd; apply/(ex5_Xij_pr x ha t).
Qed.

Definition ex5_Y J k x := intersectionf J (fun i => ex5_X i k (Vg x i)).
Definition ex5_inY J k x t := 
   forall i, inc i J -> Vg x i = Vf (ex5_f i k) t.
Definition ex5_upper_bd J k :=
  inc k (psI S) /\ (forall i, inc i J -> gle (psr S) i k). 

Lemma ex5_Y_prop1 J k x: ex5_upper_bd J k ->
   sub (ex5_Y J k x) (Vg (psE S) k).
Proof.
move => ha.
case: (emptyset_dichot J) => Jne.
  rewrite /ex5_Y Jne setIf_0; apply: sub0_set.
move: Jne => [i iJ] t ti. 
by move:(setIf_hi ti iJ); case/(ex5_Xij_pr (Vg x i) (proj2 ha _ iJ)).
Qed.

Lemma ex5_Y_prop2 J k x: nonempty J -> ex5_upper_bd J k ->
  forall t, inc t (ex5_Y J k x) <-> (inc t (Vg (psE S) k) /\ ex5_inY J k x t).
Proof.
move => ha hb t; split.
  move => tI; split; [ by apply: (ex5_Y_prop1 hb tI) | move => i iJ].
  by move:(setIf_hi tI iJ) => /(ex5_Xij_pr (Vg x i) (proj2 hb _ iJ)) [].
move => [hc hd]; apply/(setIf_P _ ha) => i iJ.
apply/(ex5_Xij_pr (Vg x i) (proj2 hb _ iJ)); split => //;fprops.
Qed. 

Definition ex5_mij_J J k x := (fun_image J (fun i => ex5_M i k (Vg x i))).
Definition ex5m J k x:= infimum (Vg Er k) (ex5_mij_J J k x).
Definition ex5_fneI J := [/\ sub J (psI S), finite_set J & nonempty J].
Definition ex5_prodG J x :=  [/\ fgraph x, domain x = J &
                 forall i, inc i J -> inc (Vg x i) (Vg Gf i)].

Section Exercise5_prop_m.
Variables J k x: Set.
Hypothesis (mp1: ex5_fneI J) (mp2: ex5_upper_bd J k)(mp3: ex5_prodG J x).

Lemma ex5m_prop1: sub (ex5_mij_J J k x) (substrate (Vg Er k)).
Proof. 
move => t /funI_P [i iJ ->].
have lij := (proj2 mp2 i iJ). 
move:(proj1 (ex5_Mij_pr1 lij ((proj33 mp3) i iJ))); rewrite (sEr (proj1 mp2)).
by case/(ex5_Xij_pr (Vg x i) lij).
Qed.


Lemma ex5m_prop2: has_infimum (Vg Er k) (ex5_mij_J J k x).
Proof. 
move:(proj1 mp2)(mp1) => jI [_ nej fsj].
have fs: finite_set (ex5_mij_J J k x) by apply: finite_fun_image.
have ne:nonempty (ex5_mij_J J k x) by apply:funI_setne.
exact: (lattice_finite_inf2 (lEr jI) fs ne ex5m_prop1).
Qed.

Lemma ex5m_prop3 y:
    (gle (Vg Er k) y (ex5m J k x) <->
     (forall i, inc i J -> gle (Vg Er k) y (ex5_M i k (Vg x i)))).
Proof.
move:(proj1 mp2)(mp1) => jI [_ nej fsj].
have fs: finite_set (ex5_mij_J J k x) by apply: finite_fun_image.
have ne:nonempty (ex5_mij_J J k x) by apply:funI_setne.
apply: (iff_trans (lattice_finite_inf3P  (lEr jI) y fs ne (ex5m_prop1))). 
split=> // hz z za.
    apply: hz; apply/funI_P; ex_tac.
by move/funI_P: za => [i iJ ->]; apply: hz.
Qed.

Lemma ex5m_prop4: inc (ex5m J k x) (Vg (psE S) k).
Proof.
move: (proj1 mp2) => kI; rewrite -(sEr kI).
exact: (inc_infimum_substrate (proj1 (lEr kI)) (ex5m_prop1) (ex5m_prop2)).
Qed.


Lemma ex5m_prop3_bis i: inc i J ->
  gle (Vg Er k)  (ex5m J k x) (ex5_M i k (Vg x i)).
Proof.
move: (proj1 mp2) => kI.
move:(ex5m_prop4); rewrite - (sEr kI) => /(proj42 (proj1 (lEr kI))).
move/(ex5m_prop3); apply.
Qed.
 
End Exercise5_prop_m.

Definition ex5_coherent1 J x :=
  [/\ ex5_fneI J, ex5_prodG J x,
   forall i j, inc i J -> inc j J -> gle (psr S) i j -> 
             Vg x i = Vf (ex5_f i j) (Vg x j) &
   forall k, ex5_upper_bd J k -> nonempty ((Vg Gf k) \cap (ex5_Y J k x))].

Lemma ex5_res1a J k x:
  ex5_coherent1 J x  -> ex5_upper_bd J k ->
  greatest (induced_order (Vg Er k) (ex5_Y J k x)) (ex5m J k x).
Proof.
move => [fneI co2 si so] ku.
have ru:= (ex5m_prop4 fneI ku co2).
have Ha:=(ex5_Y_prop2 x (proj33 fneI) ku).
have kI:= (proj1 ku).
have orj:=(proj1 (lEr kI)).
move:(ex5_Y_prop1 ku (x:=x)); rewrite - (sEr kI) => hu.
have hv: (substrate (induced_order (Vg Er k) (ex5_Y J k x))) =  ex5_Y J k x.
   by rewrite iorder_sr.
have co3 t: inc t (ex5_Y J k x) -> gle (Vg Er k) t (ex5m J k x).
  move /Ha => [ta tb]; apply/(ex5m_prop3 fneI ku co2) => i iJ.
  have lik := (proj2 ku _ iJ).
  by apply: (proj2 (ex5_Mij_pr2 lik (proj33 co2 _ iJ)) _ ta); rewrite tb.
move:(so k ku) => [x' /setI2_P [x'G x'Y]].
have x'E:= (ex5_G4 kI x'G).
have co4: gle (Vg Er k) x' (ex5m J k x) by apply:co3.
suff imY: inc (ex5m J k x) (ex5_Y J k x).
  hnf; rewrite hv; split => // t tY; apply/iorder_gleP; split; fprops.
apply/Ha; split; [ apply: ru | move => i iJ].
move:(proj2 ku _ iJ) => lik.
have iI:= (proj1 (prl_prop0 lik)).
move:(fm lik); aw; move =>[ork ori] _ fincr.
move:(fincr _ _ (ex5m_prop3_bis fneI ku co2 iJ)). 
move /(ex5_Y_prop2 _ (proj33 fneI) ku): x'Y => [_ x'p].
move:(fincr _ _ co4); rewrite - (x'p _ iJ). 
rewrite(proj1 (ex5_Mij_pr2 lik (proj33 co2 i iJ))) => qa qb; order_tac.
Qed.

Lemma ex5_res1b J k x:
  ex5_coherent1 J x  -> ex5_upper_bd J k ->
  (Vg Gf k) \cap (ex5_Y J k x) =
  Zo (Vg Gf k) (fun y => gle (Vg Er k) y (ex5m J k x)).
Proof.
move => ha ku.
move:(ex5_res1a ha ku) => mp.
move: ha =>  [fneI co2 si _].
have ru:= (ex5m_prop4 fneI ku co2).
have Ha:=(ex5_Y_prop2 x (proj33 fneI) ku).
have kI:= (proj1 ku).
move:(ex5_Y_prop1 ku (x:=x)); rewrite - (sEr kI) => hu.
case: mp; rewrite (iorder_sr (proj1 (lEr kI)) hu) => imY co3.
set_extens t.
  by move/setI2_P => [ta /co3/iorder_gle1  tb]; apply/Zo_P.
move/Zo_P => [ta tb]; apply/setI2_P;split => //.
apply/Ha; split => //; first by apply: ex5_G4.
move => i iJ.
move:(proj2 ku _ iJ) => lik.
have iI:= (proj1 (prl_prop0 lik)).
move:(fm lik); aw; move =>[ork ori] _ fincr.
move:(ex5m_prop3_bis fneI ku co2 iJ) => le1.
have le2: gle (Vg Er k) t (ex5_M i k (Vg x i)) by order_tac.
symmetry;ex_middle bad.
move:(fincr _ _ le2).
rewrite (proj1 (ex5_Mij_pr2 lik (proj33 co2 i iJ))) => le3.
by case:(ex5_G5 iI (ex5_Gij_prop1 lik ta) (proj33 co2 i iJ) bad); left.
Qed.

Definition finite_ne_sub K J := [/\ finite_set K, nonempty K & sub K J].
Definition ex5_coherent2 x :=
  [/\  ex5_prodG (domain x) x, sub (domain x) (psI S) &
  forall K, finite_ne_sub K (domain x) -> ex5_coherent1 K (restr x K) ].

Definition ex5_extend x j a := (x +s1 (J j a)).
Definition ex5_extend_prop x j x':= ex5_coherent2 (ex5_extend x j x').


Lemma ex5_res2 x j:
  ex5_coherent2 x -> inc j (psI S) -> domain x = emptyset ->
  exists x', ex5_extend_prop x j x'.
Proof.
move => [[ha hb hc] _ _] jI je. 
move:(ex5_G3 jI) =>[x' x'G].
have jj: ~inc j (domain x) by rewrite je => /in_set0.
set J := domain x.
have ha': fgraph (ex5_extend x j x') by apply:fgraph_setU1.
have hb': domain (ex5_extend x j x') = J +s1 j by rewrite /J domain_setU1 . 
have vv: (Vg (ex5_extend x j x') j) = x' by rewrite setU1_V_out //.
have vg: inc (Vg (ex5_extend x j x') j) (Vg Gf j) by rewrite vv.
have dd: domain (ex5_extend x j x') = singleton j by rewrite hb' /J je set0_U2. 
have sdx: sub (domain (ex5_extend x j x')) (psI S). 
  by rewrite dd => t /set1_P ->.
have co: ex5_prodG (domain (ex5_extend x j x')) (ex5_extend x j x').
  by rewrite dd;split => // i /set1_P ->; rewrite vv. 
exists x'; split=> // K [fsK neK];rewrite hb' /J je set0_U2 => /subset1P; case.
  by move => ke;case/nonemptyP: neK.
move ->.
have: (restr (ex5_extend x j x') (singleton j)) =  (ex5_extend x j x').
  by rewrite -{2} (restr_to_domain ha' (@sub_refl (ex5_extend x j x'))) dd.
move ->;split.
- split;[ by move => t /set1_P -> | apply:set1_finite | fprops ].
- by split; [ |   | move => i /set1_P -> ].
- move => j1 j2 /set1_P -> /set1_P -> lee; rewrite vv.
  by rewrite /ex5_f (ps_identity_f jI) idV//; apply:(ex5_G4 jI).
- move => k kip; move:((proj2 kip) _ (set1_1 j)) => lejk.
  move:(ex5_Gij_prop2 lejk x'G)=> [t ta tb].
  have nej: nonempty (singleton j) by fprops.
  exists t; apply/setI2_P; split => //; apply/(ex5_Y_prop2 _ nej kip).
  split; first  by apply:(ex5_G4 (proj1 kip)). 
  by move => i /set1_P ->; rewrite vv. 
Qed.

Section Exercise5b.
Variables j x: Set.
Let J' := domain x.
Hypothesis coh2: ex5_coherent2 x.
Hypothesis jJ : inc j (psI S) /\ ~ (inc j J').
Hypothesis Jne: nonempty J'.

Definition ex5_b_prop F k := 
  [/\ finite_ne_sub F J',  ex5_upper_bd F k &  gle (psr S) j k].

Lemma ex5_res3 F k (f := (ex5_f j k))
      (T:= Vfs f ((Vg Gf k) \cap (ex5_Y F k (restr x F)))):
  ex5_b_prop F k ->
  nonempty T /\ 
  T = Zo (Vg Gf j) (fun t => gle (Vg Er j) t (Vf f (ex5m F k (restr x F)))).
Proof.
move => [fnsFJ ubKn lejk].
move: ((proj33 coh2) _ fnsFJ) => co1.
move:(prl_prop0 lejk) => [jI kI].
move:(prl_prop4 lejk) => [fjk sjk tjk].
have pa: sub (Vg Gf k) (source (ex5_f j k)).
  by move => t; rewrite sjk; apply:ex5_G4.
have pb:= (sub_trans (@setI2_1 (Vg Gf k) (ex5_Y F k (restr x F))) pa).
split; first by apply: (nonempty_image fjk _ pb); exact: (proj44 co1 _ ubKn).
have pc:=(ex5_res1b co1 ubKn).
set_extens t.
  move/(Vf_image_P fjk pb)=> [u uGY ->].
  move /setI2_P:(uGY) => [/(ex5_Gij_prop1 lejk) uG uY].
  move: uGY; rewrite pc => /Zo_P [_ le1].
  by apply/Zo_P; split => //; move:(fm lejk) => [or1 or2 _]; aw; apply.
move => /Zo_P [tG le1].
have mE:=(ex5m_prop4 (proj41 co1) ubKn (proj42 co1)).
have hh: exists2 y, inc y (Vg Gf k) & gle (Vg Er k) y (ex5m F k (restr x F)).
  move:(proj44 co1 _ ubKn).
  rewrite pc; move => [y /Zo_P [ya yb]]; ex_tac.
move:(ex5_G8 lejk mE hh tG le1) =>  [x' [x'G le2 vv]].
apply/(Vf_image_P fjk pb); rewrite pc.
by exists x' => //; apply/Zo_P.
Qed.

Lemma ex5_res4: exists F0 k0,
    ex5_b_prop F0 k0 /\
     forall F k, ex5_b_prop F k ->
     gle (Vg Er j) (Vf (ex5_f j k0) (ex5m F0 k0 (restr x F0)))
         (Vf (ex5_f j k) (ex5m F k (restr x F))).
Proof. 
pose mm F k := (Vf (ex5_f j k) (ex5m F k (restr x F))).
have T := (proj33 (ps_preorder_r S)).
have jI:= (proj1 jJ).
have or:= (proj1 (lEr jI)).
have hu F k k': ex5_b_prop F k -> gle (psr S) k k' ->  ex5_b_prop F k'.
  move =>  [ff ubk lejk] lekk'.
  split=> //.
    split; first  exact: (proj2 (prl_prop0 lekk')).
    move => i /(proj2 ubk) => la; exact:(T _ _ _ la lekk').
  exact:(T _ _ _ lejk lekk').
have hv F k: ex5_b_prop F k -> inc (mm F k) (Vg (psE S) j).
  move => [ff ubk lejk]. 
  have hb:=(proj33 coh2 F ff).
  move: ff=> [fsF neF sFJ].
  have fne: ex5_fneI F by split => //; apply:(sub_trans sFJ (proj32 coh2)).
  have co2: ex5_prodG F (restr x F).
    split => //; aww => i iF; rewrite LgV//; apply:(proj33 (proj31 coh2)).
    by apply: sFJ.
  move:(ex5m_prop4 fne ubk co2) => me.
  by rewrite /mm/ex5_f; move: (prl_prop4 lejk) => [ff sf tf]; Wtac.
have Ha F k k':  ex5_b_prop F k -> gle (psr S) k k' -> 
  gle (Vg Er j) (mm F k') (mm F k).
  move => pa lekk'; move:(proj32 (hu _ _ _ pa lekk')) => ubk'.
  move:pa => [ff ubk lejk].
  have hb:=(proj33 coh2 F ff).
  move: ff=> [fsF neF sFJ].
  have fne: ex5_fneI F by split => //; apply:(sub_trans sFJ (proj32 coh2)).
  have co2: ex5_prodG F (restr x F).
    split => //; aww => i iF; rewrite LgV//; apply:(proj33 (proj31 coh2)).
    by apply: sFJ.
  rewrite /mm -(prl_prop3 lejk lekk' (ex5m_prop4 fne ubk' co2)).
  move:(fm lejk); aw; move =>[ork orj _]; apply.
  move: (prl_prop0 lekk') =>[kI kI'].
  have ork' := (proj1 (lEr kI')).
  have sy1: sub (ex5_Y F k (restr x F)) (substrate (Vg Er k)).
    by rewrite (sEr kI);  apply: ex5_Y_prop1. 
  have sy2: sub (ex5_Y F k' (restr x F)) (substrate (Vg Er k')).
    by rewrite (sEr kI');  apply: ex5_Y_prop1. 
  move: (ex5_res1a hb ubk) (ex5_res1a hb ubk'). 
  set m := ex5m _ _ _; set m' := ex5m _ _ _.
  rewrite /greatest (iorder_sr ork sy1) (iorder_sr ork' sy2).
  move => [mY' maxm'][mY maxm].
  suff  ww: inc (Vf (Vg (psf S) (J k k')) m') (ex5_Y F k (restr x F)).
     exact: (iorder_gle1(maxm' (Vf (Vg (psf S) (J k k')) m') ww)).
  move: (prl_prop4 lekk') =>[fkk skk tkk].
  have fkkmE: inc (Vf (Vg (psf S) (J k k')) m') (Vg (psE S) k).
     by Wtac; rewrite skk;move:(sy2 _ mY); rewrite (sEr kI').
  apply /(ex5_Y_prop2 _ neF ubk); split => //.
  move => i iF; rewrite LgV//.
  move/(ex5_Y_prop2 _ neF ubk'): mY => [mu] h; move: (h _ iF); rewrite LgV//.
  by rewrite (prl_prop3  (proj2 ubk i iF) lekk' mu).
have Hb: forall F F' k, ex5_b_prop F k ->  ex5_b_prop F' k -> sub F F'
     -> gle (Vg Er j) (mm F' k) (mm F k).
  move => F F' k  [ff ubk lejk]  [ff' ubk' _] sff.
  move:(fm lejk); aw; move =>[ork orj _]; apply.
  have hb:=(proj33 coh2 F ff).
  have hb':=(proj33 coh2 F' ff').
  have kI:= (proj1 ubk).
  move: (ex5_res1a hb ubk) (ex5_res1a hb' ubk').
  have sy1: sub (ex5_Y F k (restr x F)) (substrate (Vg Er k)).
     by rewrite (sEr kI);  apply: ex5_Y_prop1. 
  have sy2: sub (ex5_Y F' k (restr x F')) (substrate (Vg Er k)).
     by rewrite (sEr kI);  apply: ex5_Y_prop1. 
  set m := ex5m _ _ _; set m' := ex5m _ _ _.
  rewrite /greatest (iorder_sr ork sy1) (iorder_sr ork sy2).
  move => [mY maxm][mY' maxm'].
  suff: inc m' (ex5_Y F k (restr x F))  by move/maxm => /iorder_gle1.
  move/(ex5_Y_prop2 (restr x F') (proj32 ff') ubk'): mY' => [qa qb].
  apply/(ex5_Y_prop2 _ (proj32 ff) ubk); split => // i iF; rewrite LgV//.
  move:(sff _ iF) => iF'; rewrite -(qb _ iF'); rewrite LgV//.
have Hc F F' k k': ex5_b_prop F k ->  ex5_b_prop F' k' ->
  exists F'' k'', [/\  ex5_b_prop F'' k'',
  gle (Vg Er j) (mm F'' k'') (mm F k) & gle (Vg Er j) (mm F'' k'') (mm F' k')].
  move => pa pb; move:(pa)(pb) => [ff ubk lejk]  [ff' ubk' lejk'].
  move: (proj1 ubk) (proj1 ubk'); rewrite - ps_substrate_r => kr kr'.
  move:(rdr kr kr') =>[k'' [le1 le2]].
  set F'' := F \cup F'.
  have neF'': nonempty F'' by move:(proj32 ff) =>[t tf]; exists t;apply:setU2_1.
  have ra: ex5_b_prop F'' k''.
    move:ff ff' =>[qa qb pc][pe pf pg].
    split.
    + by split; [ apply:finite_U2 | exact | apply:setU2_12S].
    +  split; first exact:(proj2 (prl_prop0 le1)).
       move => i/setU2_P; case => ii.
         exact:(T _ _ _ (proj2 ubk _ ii) le1).
         exact:(T _ _ _ (proj2 ubk' _ ii) le2).
    + exact:(T _ _ _ lejk le1).
  set T'' := proj43 or.
  move:(Ha _ _ _ pa le1) (Ha _ _ _ pb le2) => la lb.
  move:(Hb F F'' k'' (hu F k k'' pa le1) ra (@subsetU2l F F')) => lc.
  move:(Hb F' F'' k'' (hu F' k' k'' pb le2) ra (@subsetU2r F F')) => ld.
  exists F'', k'';split => //.
    exact:(T'' _ _ _ lc la).
    exact:(T'' _ _ _ ld lb).
set A := Zo (Vg (psE S) j) (fun z => exists F k, 
  ex5_b_prop F k /\ z = mm F k).
have Ap1: forall m m', inc m A -> inc m' A ->
     exists m'', [/\ inc m'' A, gle (Vg Er j) m'' m & gle (Vg Er j) m'' m'].
  move => m m' /Zo_P[mE [F [k [pa pb]]]] /Zo_P[mE' [F' [k' [pa' pb']]]].
  move:(Hc _ _ _ _ pa pa') => [F'' [k'' [ra rb rc]]].
  rewrite pb pb'; exists (mm F'' k''); split => //; apply/Zo_P; split.
    by move:(arg1_sr rb); rewrite (sEr jI).
  by exists F'', k''.
have neA: nonempty A.
  move:Jne =>[i iJ].
  have iI:= (proj32 coh2 _ iJ).
  move: iI jI; rewrite - ps_substrate_r => ir jr.
  move:(rdr ir jr) =>[k [le1 le2]].
  have pp: ex5_b_prop (singleton i) k.
    split.
    + by split; [ apply: set1_finite | apply:set1_ne | apply:set1_sub].
    + by split; [exact (proj2 (prl_prop0 le1)) | move => t /set1_P ->].
    + exact.
  exists (mm (singleton i) k); apply:Zo_i; first by apply: hv.
  by exists (singleton i), k.
have ap1: sub A (Vg (psE S) j) by apply: Zo_S.
have ap2: sub A (substrate (Vg Er j)) by rewrite sEr.
move:(sen jI ap1 neA) => [a[]].
rewrite (iorder_sr or ap2) => aA amin.
move/Zo_P: (aA) => [aeJ [F [k [fkp  ffv]]]]; exists F,k; split => //.
move => F' k' fkp'; rewrite - /(mm F k) - ffv.
have bA: inc (mm F' k') A by  apply:Zo_i; [ by apply: hv | exists F', k'].
move:(Ap1 _ _ aA bA) => [c [cA le1 le2]].
by move/(iorder_gle0P  (Vg Er j) cA aA): le1 => /amin <-.
Qed.



Lemma ex5_res5: exists x', ex5_extend_prop x j x'.  
Proof.
move:ex5_res4 => [F0 [k0 [Fk0p F0k0min]]].
move:jJ =>[jI jd].
move:(ex5_res3 Fk0p) => [[x' xe] xf]; exists x'.
move:xe; rewrite xf => /Zo_P [xG' lexfm].
have Ha F k: ex5_b_prop F k -> exists u, [/\ inc u (Vg Gf k), 
    inc u (ex5_Y F k (restr x F)) & x' = Vf (ex5_f j k) u].
  move => hF.
  move: (F0k0min _ _ hF) => eq2.
  move: (proj43 (proj1 (lEr jI)) _ _ _ lexfm eq2) => lee.
  move: (prl_prop4 (proj33 hF)) =>[fjk sjk tjk].
  move:(proj2 (ex5_res3 hF));set T := Zo _ _ => eqq.
  have kI:=(proj1 (proj32 hF)).
  have ss: (sub (Vg Gf k \cap ex5_Y F k (restr x F)) (source (ex5_f j k))). 
   by rewrite sjk => t /setI2_P [/(ex5_G4 kI)].
  have: inc x' T by apply/Zo_P.
  rewrite - eqq; move/(Vf_image_P fjk ss) =>[u /setI2_P [uG up] uv].
  by exists u.
clear xf lexfm F0k0min.
have Hb i: inc i (domain x) -> gle (psr S) j i -> 
   x' = Vf (ex5_f j i) (Vg x i). 
  move => idx leij; move: (set1_1 i) => isi.
  have iI:= proj2 (prl_prop0 leij).
  have hu:ex5_upper_bd (singleton i) i.
    split => // t /set1_P ->.
    by apply:(proj32 (ps_preorder_r S) i); rewrite ps_substrate_r.
  have Hsi: ex5_b_prop (singleton i) i.
    split => //.
    + by split; [apply: set1_finite | apply:set1_ne | move => t /set1_P ->].
  move:(Ha _ _ Hsi) => [u [ua ub uc]]. 
  move/(ex5_Y_prop2 _ (set1_ne i) hu): ub => [uu hi].
  move:(hi i (set1_1 i)); rewrite LgV//.
  by rewrite uc /ex5_f (ps_identity_f iI); rewrite idV // => ->.
have Hc i: inc i (domain x) -> gle (psr S) i j -> 
   (Vg x i) = Vf (ex5_f i j) x'.
  move => idx leij.
  have hu:ex5_upper_bd (singleton i) j by split => // t /set1_P ->.
  have Hsi: ex5_b_prop (singleton i) j.
    split => //.
    + by split; [apply: set1_finite | apply:set1_ne | move => t /set1_P ->].
    + by apply:(proj32 (ps_preorder_r S) j); rewrite ps_substrate_r.
  move:(Ha _ _ Hsi) => [u [ua ub uc]]. rewrite uc /ex5_f (ps_identity_f jI).
  move/(ex5_Y_prop2 _ (set1_ne i) hu): ub => [uu hi].
  move:(hi i (set1_1 i)); rewrite LgV// ? idV//; fprops.
have xE': inc x' (Vg (psE S) j) by apply: ex5_G4.
move: coh2 =>[[fgx _ xG] dxI co1xk].
have Vout:(Vg (ex5_extend x j x') j) = x' by rewrite (setU1_V_out _ fgx jd).
have dsI:sub (domain (ex5_extend x j x')) (psI S).
  by rewrite domain_setU1; apply:setU1_sub.
have ra:ex5_prodG (domain (ex5_extend x j x')) (ex5_extend x j x').
  aw; split.
  + apply:fgraph_setU1 => //.
  + reflexivity.
  + rewrite domain_setU1 => i /setU1_P; case => iJ; last by rewrite iJ Vout.
    by rewrite (setU1_V_in _ fgx jd iJ); apply: xG.
split => // K [fsK neK kJj].
have sKI:=(sub_trans kJj dsI).
have rb:ex5_prodG K (restr (ex5_extend x j x') K).
  split => //; aww => i iK; rewrite LgV//; exact: (proj33 ra _ (kJj _ iK)).
set K':= K -s1 j.
case: (emptyset_dichot K') => kne.
  have jj:= (set1_1 j).
  have hj:Vg (restr (ex5_extend x j x') (singleton j)) j = x' by rewrite LgV//; ue.
  have Kv: K = singleton j.
    by apply:(set1_pr1 neK)=> t tK; ex_middle kj; empty_tac1 t; apply/setC1_P.
  split => //.
    rewrite Kv => j1 j2 /set1_P -> /set1_P -> lejj.
    rewrite hj /ex5_f ps_identity_f //; rewrite idV//.
  move => k [kI ljk1]; rewrite Kv.
  have ljk: gle (psr S) j k by apply: ljk1; rewrite  Kv.
  move: (ex5_Gij_prop2 ljk xG')  => [t ta tb].
  have hh: ex5_upper_bd (singleton j) k by split => // i /set1_P ->.
  exists t; apply/setI2_P; split => //;apply/(ex5_Y_prop2 _ (set1_ne j) hh).
  split; first by apply:(ex5_G4 kI). 
  by  move => i /set1_P ->; rewrite hj. 
move: kJj; rewrite domain_setU1 => kJj.
have KK: sub K' K by apply: sub_setC.
have KJ':sub K' J' by move => t/setC1_P [ /kJj /setU1_P]; case.
have fneK': finite_ne_sub K' J' by split => //; apply: sub_finite_set fsK.
move:(co1xk _ fneK') =>[sa sb sc sd].
have Kp i: inc i K -> i <> j -> inc i J' by  move/(kJj) => /setU1_P; case.
split => //.
    move => j1 j2 j1K j2K lej1j2; rewrite !LgV//.
    case: (equal_or_not j1 j) => j1p;case: (equal_or_not j2 j) => j2p.
    + rewrite j1p j2p  (setU1_V_out _ fgx jd).
      have kK: inc j K by ue.
      rewrite /ex5_f (ps_identity_f jI) idV//.
    + rewrite j1p (setU1_V_out _ fgx jd).
      have j2dx: inc j2 (domain x) by apply:Kp.
      rewrite (setU1_V_in _ fgx jd j2dx); apply: Hb => //; ue.
    + rewrite j2p (setU1_V_out _ fgx jd).
      have j1dx: inc j1 (domain x) by apply: Kp.
      rewrite (setU1_V_in _ fgx jd j1dx); apply: Hc => //; ue.
    + have j1dx: inc j1 (domain x) by apply: Kp.
      have j2dx: inc j2 (domain x) by apply:Kp.
      rewrite (setU1_V_in _ fgx jd j2dx) (setU1_V_in _ fgx jd j1dx).
      have j1K': inc j1 K' by apply/setC1_P.
      have j2K': inc j2 K' by apply/setC1_P.
      move:(sc _ _ j1K' j2K' lej1j2); rewrite ! LgV//.
move => k.
case: (inc_or_not j K) => jK; last first.
  rewrite -(setC1_eq jK) -/K'; move:(sd k) => qa qb.
  have ->: restr (ex5_extend x j x') K' = restr x K'.
    apply:fgraph_exten; aww => t tK'; rewrite ! LgV//.
    by rewrite (setU1_V_in _  fgx jd) //;apply: KJ'.
  exact: (qa qb). 
move => [kI ubk].
have ha': ex5_upper_bd K' k by split => //i /KK/ubk.
have lejk: gle (psr S) j k by exact:(ubk _ jK).
have ex5bp: ex5_b_prop K' k by split.
move:(Ha K' k ex5bp) => [u [uG up uv]].
exists u; apply/setI2_P; split => //. apply/(ex5_Y_prop2 _ neK (conj kI ubk)).
split; first by apply:(ex5_G4 kI). 
move => i iK; rewrite LgV//.
case:(equal_or_not i j) => nij; first by rewrite nij Vout. 
have iK': inc i K' by apply/setC1_P.
have idx: inc i (domain x) by apply: KJ'.
rewrite (setU1_V_in _ fgx jd idx).
move/(ex5_Y_prop2 _ kne ha'): up => [ssa ssb].
rewrite - (ssb _ iK'); rewrite LgV//.
Qed.

End Exercise5b.

Lemma ex5_result: nonempty (projective_limit  ex5_S').
Proof.
suff: exists2 x, ex5_coherent2 x & domain x = psI S.
  move => [x  [[pa _ pc] _ pd] dx]; rewrite dx in pc pd.
  rewrite prl_subsets_prop2; exists x; apply /setI2_P; split.
     apply/prl_limitP; split => //.
       move => i iI; exact:(ex5_G4 iI (pc _ iI)).
     move => i j leij.
     move:(prl_prop0 leij) => [iI jI]. 
     move: (set2_1 i j) (set2_2 i j) => di dj.
     have fsd: finite_ne_sub (doubleton i j) (psI S).
       by split; [ apply:set2_finite | apply:set2_ne | apply:sub_set2]. 
     move:(pd _ fsd) => [_ _] h; move:(h _ _ di dj leij); rewrite !LgV//.
  by apply/setXb_P; rewrite ex5_G2.
set Y0:= sub_fgraphs (psI S) (unionb Gf).
have Y0_p: forall x, ex5_coherent2 x -> inc x Y0.
  move => x [[ha1 ha2 ha3] hb _]; apply/sub_fgraphsP; exists (domain x) => //.
  apply/ gfunctions_P2; split => // t/(range_gP ha1) [i idx ->].
  by apply/setUb_P; rewrite ex5_G2; exists i => // ; [apply: hb | apply: ha3].
set Y := Zo Y0 ex5_coherent2.  
have Y_p: forall x, inc x Y <-> ex5_coherent2 x.
    move => x; split;[ by case/Zo_P | move => h; apply:(Zo_i (Y0_p _ h) h)].
have aux: sub Y (\Po (union Y)).
  move => t tA; apply/setP_P => x xt; union_tac.
have aux2:forall X,
     (forall x y, inc x X -> inc y X -> sub x y \/ sub y x) ->
     sub X Y -> inc (union X) Y. 
  move => X ha hb; apply/Y_p.
  have hc: sub (domain (union X)) (psI S).
    move=> t /funI_P [z /setU_P [y zy /hb /Y_p yX] ->].
    move: yX => [_ dx _]; apply:dx; apply/funI_P; ex_tac.
  have hd: sgraph (union X).
    move => t /setU_P [y ty  /hb /Y_p [[ra _ _ ] _ _]]; exact: (proj1 ra _ ty).
  have he: fgraph (union X).
    split => // a b /setU_P [y ay yX] /setU_P [y' by' yX'] sp.
    move/hb:(yX) => /Y_p [[ra _ _ ] _ _];move/hb:(yX') => /Y_p [[rb _ _ ] _ _].
    case:(ha _ _ yX yX') => syy.
      by move:(proj2 rb _ _ (syy _ ay) by' sp).
      by move:(proj2 ra _ _ ay (syy _ by') sp).
  have Hb z t: inc z t -> inc t X -> Vg (union X) (P z) = Vg t (P z).
     move => zt tX. 
     have tU: sub t (union X) by move => i it; apply/setU_P; exists t.
     rewrite -(restr_to_domain he tU); rewrite LgV//; apply/funI_P; ex_tac.
  have hf i: inc i (domain (union X)) -> inc (Vg (union X) i) (Vg Gf i).
    move => /funI_P [z /setU_P [t zt tX] ->]; rewrite (Hb _ _ zt tX).
   move/hb:(tX) => /Y_p [[_ _  rc ] _ _]; apply: rc; apply/funI_P; ex_tac.
  have hg:ex5_prodG (domain (union X)) (union X) by [].
  split => // K [fsk nek sk].
  have [t ta tb]: exists2 t, inc t X & sub K (domain t).
    pose A K := sub K (domain (union X)).
    pose B K := exists2 t, inc t X & sub K (domain t).
    have hi a: A (singleton a) -> B (singleton a).
      rewrite /A/B=> hh.
      move:(hh _ (set1_1 a)) => /funI_P [z /setU_P [y zy yx] ->]; ex_tac.
      move => t/set1_P ->; apply/funI_P; ex_tac.
    apply:(finite_set_induction2 (A:= A) (B := B) hi _ fsk nek sk).
    move => a b hu ane hv.
    have hw: A a by move => t ta; apply: hv; fprops.
    move:(hu ane hw) => [t1 t1X t1a].
    have: inc b (domain (union X)) by apply:hv; fprops.
    move => /funI_P [z/setU_P [t2 zt2 t2X] bv].
    have t2b: inc b (domain t2) by apply/funI_P; ex_tac.
    case: (ha _ _ t1X t2X) => /domain_S t1t2.
      exists t2 => // t/setU1_P; case => hq;[ by apply:t1t2; apply: t1a| ue].
      exists t1 => // t/setU1_P; case => hq;[ by apply: t1a | apply:t1t2; ue].
  have ->: (restr (union X) K) = restr t K.
    have tU: sub t (union X) by move => i it; apply/setU_P; exists t.
    by rewrite -(restr_to_domain he tU); rewrite double_restr.
  by move/hb:(ta) => /Y_p [_ tra rb]; apply: rb.
move: (setP_maximal aux aux2) => [x []].
rewrite (proj2 (sub_osr Y)) => /Y_p co2 xmax.
case: (equal_or_not (domain x) (psI S)) => dx; first by exists x.
have /setC_ne [j /setC_P jp]: ssub(domain x)(psI S)
 by split => //; exact: (proj32 co2).
have [x' x'p]: (exists x' : Set, ex5_extend_prop x j x').
   case: (emptyset_dichot (domain x)) => xe.
   apply:(ex5_res2 co2 (proj1 jp) xe).
  exact: (ex5_res5 co2 jp xe). 
have:  gle (sub_order Y) x ((ex5_extend x j x')).
  apply/sub_gleP; split; (try apply/Y_p => //); rewrite /ex5_extend; fprops.
move/xmax => /(f_equal domain). rewrite /ex5_extend domain_setU1 => eqb.
case: (proj2 jp); rewrite - eqb; fprops.
Qed.
  
End Exercise5.

Section Exercise6.

Variables I rI L rL Jf: Set.
Variable S: inductive_system.

Hypothesis rS: (isr S = rI).
Hypotheses (HIs: substrate rI = I).
Hypotheses (HLp :preorder rL)
           (HLs: substrate rL = L)
           (HLd:right_directed_on rL L).
Hypothesis (HJg: fgraph Jf)
           (HJd: domain Jf = L)
           (HJI: unionb Jf = I)
           (HJm: forall i j, gle rL i j -> sub (Vg Jf i) (Vg Jf j))
           (HJrd: forall j, inc j L -> right_directed_on rI (Vg Jf j)).
  
Lemma ex6_prop1 i: inc i L -> sub (Vg Jf i) I.
Proof.
by rewrite - HJI => iL t tu; apply/setUb_P; rewrite HJd; ex_tac.
Qed.

Lemma ex6_prop2 i j: gle rL i j -> inc i L /\ inc j L.
Proof. by move => lij; move:(arg1_sr lij) (arg2_sr lij); rewrite HLs. Qed.

Lemma ex6_prop3: I = isI S.
Proof. by rewrite - HIs - is_substrate_r rS. Qed.

Lemma ex6_prop4 i:inc i L -> sub_right_directed (Vg Jf i) (isr S).
Proof.
rewrite rS;move => iL;split; last by apply: HJrd.
by rewrite HIs; apply: ex6_prop1.
Qed.

Definition ex6_systemi i:=
  match (ixm (inc i L)) with
    | inl hx => (inl_restr (ex6_prop4 hx))
    | inr _ => S
end.

Definition ex6_Fl i := inductive_limit (ex6_systemi i).

Lemma ex6_res0 i (H: inc i L):
  ex6_Fl i = inductive_limit (inl_restr (ex6_prop4 H)).
Proof.
by rewrite /ex6_Fl /ex6_systemi;case: (ixm (inc i L)).
Qed.

Lemma ex6_prop5a i (H:inc i L):
  inl_same_data (ex6_systemi i) (inl_restr (ex6_prop4 H)).
Proof. by rewrite /ex6_systemi; case: (ixm (inc i L)) => //. Qed.

Lemma ex6_prop5b i (Si := (ex6_systemi i)):  inc i L ->
      [/\ isE Si = restr (isE S) (Vg Jf i),
       isI Si = Vg Jf i,
       isr Si = induced_order (isr S) (Vg Jf i)&
       isf Si =  restr (isf S) (induced_order (isr S) (Vg Jf i))].
Proof.
by move=> H;rewrite /Si/ex6_systemi; case: (ixm (inc i L)).
Qed.

Lemma ex6_prop5c i j: gle rL i j ->
  sub_right_directed (Vg Jf i) (isr (ex6_systemi j)).
Proof.
move => lij.
have [iL jL] := (ex6_prop2 lij).
have ha: sub (Vg Jf j) (substrate (isr S)).
  by move: (ex6_prop1 jL); rewrite is_substrate_r ex6_prop3.
rewrite (proj43 (ex6_prop5b jL)).
split; first by rewrite (ipreorder_sr (is_preorder_r S) ha); exact: (HJm lij).
move => a b aJi bJi.
move:(HJrd iL aJi bJi) => [z [za zb zc]].
move: (HJm lij aJi) (HJm lij bJi) (HJm lij za) => aJj bJj zJj.
by exists z; split => //;apply/iorder_gleP; split => //; rewrite rS.
Qed.

Lemma ex6_prop5d i j (H:gle rL i j):
  inl_same_data (ex6_systemi i) (inl_restr (ex6_prop5c H)).
Proof.
move:(arg1_sr H) (arg2_sr H); rewrite HLs => iL jL.
move: (HJm H) => ss.
rewrite /inl_same_data.  simpl.
move:(ex6_prop5b iL)(ex6_prop5b jL) => [-> _ -> ->] [-> _ -> ->].
rewrite (iorder_trans _ ss) (double_restr _ ss) double_restr //.
by move => p /setI2_P [ha hb]; apply/setI2_P; split => //;apply:(setX_Sll ss).
Qed.

Lemma ex6_prop6a i (H:inc i L): 
  inl_equiv (ex6_systemi i) =  inl_equiv (inl_restr (ex6_prop4 H)).
Proof. exact:(inl_equiv_Iv (ex6_prop5a H)). Qed.

Lemma ex6_prop6b  i j (H:gle rL i j): 
  inl_equiv (ex6_systemi i) = inl_equiv (inl_restr (ex6_prop5c H)).
Proof. exact:(inl_equiv_Iv (ex6_prop5d H)). Qed.



Lemma ex6_res1 i j (H: gle rL i j):
  ex6_Fl i = inductive_limit (inl_restr (ex6_prop5c H)).
Proof.  apply: (inductive_limit_Iv (ex6_prop5d  H)). Qed.


Definition ex6_gij ij :=
  inductive_map (ex6_systemi (P ij))
                (Lg (Vg Jf (P ij))  (inl_can_fun (ex6_systemi (Q ij))))
                (inductive_limit (ex6_systemi (Q ij))).

Lemma ex6_gij_prop1 i j (H:gle rL i j):
   ex6_gij (J i j) = inl_restr_cf (ex6_prop5c H).
Proof.
by rewrite /ex6_gij pr1_pair pr2_pair /inl_restr_cf /inductive_map - ex6_res1.
Qed.
 
Lemma ex6_res2 i j: gle rL i j ->
  function_prop (ex6_gij (J i j))  (ex6_Fl i) (ex6_Fl j).
Proof.
move => H.
rewrite  ex6_gij_prop1 (ex6_res1 H).
exact:(inl_restr_cf_compat2 (ex6_prop5c H)).
Qed.

Lemma ex6_res3 i: inc i L -> ex6_gij (J i i) = identity (ex6_Fl i).
Proof.
move => iL. 
have H: gle rL i i by apply:(proj32 HLp); rewrite HLs.
apply: (identity_prop0 (ex6_res2 H)) => x xs.
rewrite (ex6_gij_prop1 H).
move: xs; rewrite (ex6_res1 H) => /inductive_limit_hi /= [ha]; rewrite !LgV//  => hb ->.
by rewrite (inl_restr_cf_ev (ex6_prop5c H) ha hb) (ex6_prop6b H).
Qed.

Lemma ex6_res4 i j k: gle rL i j ->  gle rL j k ->
   ex6_gij (J j k) \co ex6_gij (J i j) = ex6_gij (J i k).
Proof.
move => lij ljk; move: (proj33 HLp _ _ _ lij ljk) => lik.
move:(ex6_res2 lij) => [fij sij tij].
move:(ex6_res2 lik) => [fik sik tik].
move:(ex6_res2 ljk) => [fjk sjk tjk].
have cop: ex6_gij (J j k) \coP ex6_gij (J i j) by  split => //; ue.
apply:function_exten.
- by apply:compf_f.
- exact.
- by aw; ue.
- by aw; ue.
- aw; rewrite sij => x xs. 
  move: (arg1_sr lij)(arg2_sr lij) (arg2_sr ljk); rewrite HLs => iL jL kL.
  have xs': inc x (source (ex6_gij (J i j))) by ue.
  rewrite (compfV cop xs') !ex6_gij_prop1; clear cop xs'.
  move: xs; rewrite (ex6_res1 lij) => /inductive_limit_hi /= [Qx Px1 xv].
  have s1:sub (Vg Jf i) (Vg Jf j) by apply:HJm.
  have Px2:inc (P (rep x)) (Vg (isE (ex6_systemi j)) (Q (rep x))).
    move: Px1; simpl; rewrite LgV//.
  have Px3: inc (P (rep x)) (Vg (isE S) (Q (rep x))).
    by move: Px1; rewrite (proj41 (ex6_prop5b jL)) double_restr // LgV//.
  have Qx2 := s1 _ Qx.
  have Qx3:= (HJm ljk  Qx2).
  have Px4: inc (P (rep x)) (Vg (isE (ex6_systemi k)) (Q (rep x))).
    by rewrite (proj41 (ex6_prop5b kL)) LgV//.
  rewrite xv (inl_restr_cf_ev _ Qx Px2) (ex6_prop6b ljk).
  rewrite (inl_restr_cf_ev _ Qx2 Px4).
  by rewrite - (ex6_prop6b lij) (ex6_prop6b lik) inl_restr_cf_ev.
Qed.    


Definition ex6_F: inductive_system.
Proof.
apply:(@InductiveSystem (Lg L ex6_Fl) L rL (Lg rL ex6_gij)).
- exact: HLp.
- exact:HLs.
- exact: HLd.
- fprops.
- by aw.
- by fprops.
- by aw.
- move => p pL; move: (proj31 HLp _ pL) => pp. 
  move:(pr2_sr pL) (pr1_sr pL); rewrite HLs => iL jL.
  rewrite ! LgV//;move:pL;rewrite -{1 2}pp => pL; apply: (ex6_res2 pL).
- move => i j k ha hb; rewrite !LgV//; first by apply:(ex6_res4 ha hb).
  exact: (proj33 HLp _ _ _ ha hb).
- move => i iL; move: (iL); rewrite -HLs => iL'.
  move:(proj32 HLp _ iL') => ii.
  rewrite !LgV//; exact:(ex6_res3 iL).
Defined.


Lemma ex6_F_prop: inductive_system_on ex6_F (Lg L ex6_Fl) L rL (Lg rL ex6_gij).
Proof. done. Qed.

Definition ex6_F_val y i j :=
  class (inl_equiv ex6_F) (J (class (inl_equiv (ex6_systemi j)) (J y i)) j).

Lemma ex6_F_prop1 x
  (j := Q (rep x)) (i := (Q (rep (P (rep x))))) (y := P (rep (P (rep x)))):
  inc x (inductive_limit ex6_F) -> 
  [/\ inc j L, inc i (Vg Jf j),  inc y (Vg (isE S) i) & x = ex6_F_val y i j].
Proof.
move/inductive_limit_hi => []; simpl; rewrite /ex6_F_val -/j => jL h xv.
move:h; rewrite LgV//; rewrite (ex6_res0 jL) (ex6_prop6a jL).
by move/inductive_limit_hi; rewrite /= -/i -/y; move => [ha]; rewrite LgV// => hb <-.
Qed.

Lemma ex6_F_prop2 y i j j':
  inc i (Vg Jf j) -> inc y (Vg (isE S) i) -> gle rL j j' ->
   ex6_F_val y i j =  ex6_F_val  y i j'.
Proof.
move => iJl yEi lejj.
move:(arg1_sr lejj)(arg2_sr lejj); rewrite HLs => jL jL'.
move:(ex6_prop5b jL) => [ra rb _ _].
move:(ex6_prop5b jL') => [ra' rb' _ _].
have iJl': inc i (Vg Jf j') by  apply:(HJm lejj).
have cyE: inc (class (inl_equiv (ex6_systemi j)) (J y i)) (Vg (isE ex6_F) j).
     simpl;rewrite LgV//; apply: inl_class_in_lim; rewrite ?ra ?rb //; rewrite LgV//.
have cyE': inc (class (inl_equiv (ex6_systemi j')) (J y i)) (Vg (isE ex6_F) j').
  simpl; rewrite LgV//; apply: inl_class_in_lim; rewrite ?ra' ?rb' //; rewrite LgV//.
have yEj: inc y (Vg (isE (ex6_systemi j')) i).
  rewrite (proj41 (ex6_prop5b jL')); rewrite LgV//.
have jj: gle rL j' j' by apply: (proj32 HLp); rewrite HLs.
apply/inl_class_eq_bis => //; exists j'; aw; split => //=; rewrite !LgV//.
rewrite ! ex6_gij_prop1 {1}(ex6_prop6b lejj) (ex6_prop6b jj).
rewrite inl_restr_cf_ev // inl_restr_cf_ev //.
Qed.


Definition ex6_fct x :=
  let i := (Q (rep (P (rep x)))) in let y := P (rep (P (rep x))) in
  class (inl_equiv S) (J y i).

Definition  ex6_iso := Lf ex6_fct (inductive_limit ex6_F) (inductive_limit S).


Lemma ex6_fct_ax: lf_axiom ex6_fct (inductive_limit ex6_F) (inductive_limit S). 
Proof.
move => x /ex6_F_prop1 [ha hb hc _].
move: (ex6_prop1 ha hb); rewrite  ex6_prop3 => iI.
exact:(inl_class_in_lim iI hc).
Qed.

Lemma ex6_fct_fs: surjection ex6_iso. 
Proof.
apply:(lf_surjective ex6_fct_ax) => y /inductive_limit_hi.
set i :=  Q _; set z := P _; move => [iI zE ->].
move:(iI); rewrite - ex6_prop3 - HJI => /setUb_P [j]; rewrite HJd.
move => jL iJl.
set x1 := (class (inl_equiv (ex6_systemi j)) (J z i)).
set x :=  class (inl_equiv ex6_F) (J x1 j).
have x1in:  inc x1 (inductive_limit (inl_restr (ex6_prop4 jL))).
  rewrite /x1 (ex6_prop6a jL).
  apply: inl_class_in_lim => //; simpl; rewrite LgV//.
have x1Fj:  inc x1 (Vg (isE ex6_F) j) by simpl; rewrite LgV//; rewrite ex6_res0.
have xs:inc x (inductive_limit ex6_F).
  by apply:(inl_class_in_lim (S:=ex6_F) jL). 
ex_tac; rewrite /ex6_fct.
move:(inductive_limit_hi xs).
set j' := Q (rep x); set x1' := P (rep x);simpl; move => [j'L].
rewrite LgV// ex6_res0; move => yl'.
have x1Fj': inc x1' (Vg (isE ex6_F) j') by simpl; rewrite LgV//; rewrite ex6_res0.
case /inductive_limit_hi: yl'; set i':= Q _; set z':= P _.
simpl => iJl'; rewrite LgV// => zE' x1'v.
move/(inl_class_eq_bis (S:=ex6_F) jL j'L x1Fj  x1Fj') => [j'' []].
simpl; aw => lejj'' lej'j''; rewrite !LgV//.
move: (arg2_sr lejj''); rewrite HLs => jL''.
rewrite !ex6_gij_prop1 /x1 x1'v (ex6_prop6b lejj''). 
rewrite - (ex6_prop6a j'L) (ex6_prop6b lej'j'').
move:(HJm lejj'' iJl) (HJm lej'j'' iJl') => ijL'' i'jL''.
have zEj'':inc z (Vg (isE (ex6_systemi j'')) i).
  by rewrite(proj31 (ex6_prop5a jL'')) /=;rewrite LgV//.
have zE'j'':inc z' (Vg (isE (ex6_systemi j'')) i').
  by rewrite(proj31 (ex6_prop5a jL'')) /=; rewrite LgV//.
have zEj''a :inc z (Vg (isE (inl_restr (ex6_prop4 jL''))) i) by simpl;rewrite LgV//.
have zE'j''a: inc z' (Vg (isE (inl_restr (ex6_prop4 jL''))) i') by simpl;rewrite !LgV//.
have iI': inc i' (isI S).
   rewrite - ex6_prop3 - HJI; apply/setUb_P; rewrite  HJd; ex_tac.
rewrite (inl_restr_cf_ev _ iJl zEj'')  (inl_restr_cf_ev _ iJl' zE'j'').
rewrite(ex6_prop6a jL'').
move /(inl_class_eq_bis (S:=(inl_restr (ex6_prop4 jL'')))
                        ijL'' i'jL'' zEj''a zE'j''a ).
move => [i'' []]; simpl; aw; move => ha hb; rewrite ! LgV// => eq1.
apply/(inl_class_eq_bis iI iI' zE zE'); exists i'';aw.
split; [apply:(iorder_gle1 ha) | apply:(iorder_gle1 hb) |  done].
Qed.

  
Lemma ex6_fct_fi: injection ex6_iso. 
Proof.
apply:(lf_injective ex6_fct_ax).
rewrite /ex6_fct;move => x x' /ex6_F_prop1.
set j := Q _; set i := Q _; set y := P _; move =>[jL iJl yE ->].
move /ex6_F_prop1;set j' := Q _; set i' := Q _; set y' := P _.
move =>[jL' iJl' yE' ->].
move: (ex6_prop1 jL iJl)(ex6_prop1 jL' iJl'); rewrite  ex6_prop3 => iI iI'.
move/(inl_class_eq_bis iI iI' yE yE') => [i'' []]; aw => le1 le2  eq1.
move:(arg2_sr le1); rewrite rS HIs - HJI => /setUb_P [j2]; rewrite HJd.
move => j2L iJl2.
move:(HLd jL jL') => [j3 [j3L lea leb]].
move:(HLd j2L j3L) => [j4 [j4L lec led]].
move:(proj33 HLp _ _ _ lea led)(proj33 HLp _ _ _ leb led) => lejj4 lejj4'.
rewrite(ex6_F_prop2  iJl yE lejj4) (ex6_F_prop2 iJl' yE' lejj4').
move:(HJm lejj4 iJl) (HJm lejj4' iJl') => iJl4 iJl4'.
have yE4: inc y (Vg (restr (isE S) (Vg Jf j4)) i) by rewrite LgV.
have yE4': inc y' (Vg (restr (isE S) (Vg Jf j4)) i') by rewrite LgV.
have leii'': gle (induced_order (isr S) (Vg Jf j4)) i i''.
  by apply/iorder_gle0P => //; apply (HJm lec iJl2).
have lei'i'': gle (induced_order (isr S) (Vg Jf j4)) i' i''.
  by apply/iorder_gle0P => //; apply (HJm lec iJl2).
rewrite /ex6_F_val; congr (class _ (J _ j4)).
rewrite (ex6_prop6a j4L); apply/inl_class_eq_bis => //.
exists i''; aw;split => //=; rewrite !LgV //.
Qed.

Lemma ex6_fct_bp:
  bijection_prop  ex6_iso (inductive_limit ex6_F) (inductive_limit S).
Proof.
rewrite/ex6_iso; split; aw;split; [ apply: ex6_fct_fi | apply: ex6_fct_fs].
Qed.


End Exercise6.


Section Exercise7.

Variable S : inductive_system.

Definition ex7_eqv i := equivalence_associated  (inl_can_fun S i).

Lemma ex7_eqv_prop1 i: inc i (isI S) ->
   equivalence_on (ex7_eqv i) (Vg (isE S) i).
Proof.
move => iI.
move:(inl_can_fun_fp iI) => [fi si ti].
by move:(graph_ea_equivalence fi); rewrite si.
Qed.

Lemma ex7_eqv_prop2 i: inc i (isI S) ->  forall x y,
  related (ex7_eqv i) x y <->
  [/\ inc x (Vg (isE S) i), inc y (Vg (isE S) i) &
   class (inl_equiv S) (J x i) = class (inl_equiv S) (J y i)].
Proof.
move => iI x y.
move:(inl_can_fun_fp iI) => [fi si ti].
split.
  case/(ea_relatedP fi); rewrite si => xE yE.
  by rewrite  (inl_can_fun_ev iI xE)  (inl_can_fun_ev iI yE).
move => [xE yE etc]; apply/(ea_relatedP fi); rewrite si; split => //.
by rewrite  (inl_can_fun_ev iI xE)  (inl_can_fun_ev iI yE).
Qed.
  
Lemma ex7_eqv_prop3 i j: gle (isr S) i j ->
  compatible_with_equivs (Vg (isf S) (J i j)) (ex7_eqv i)(ex7_eqv j).
Proof.
move => leij.
move:(inl_prop0 leij) => [iI jI].
move:(ex7_eqv_prop1 iI) (ex7_eqv_prop1 jI) => [ha hb ][hc hd].
move: (inl_prop4 leij) => [fij sij tij].
have tij': target (Vg (isf S) (J i j)) = substrate (ex7_eqv j) by ue.
have sij': source (Vg (isf S) (J i j)) = substrate (ex7_eqv i) by ue.
apply:(compatible_with_pr2 ha hc fij tij' sij').
move => x y /(ex7_eqv_prop2 iI) [xE yE sc].
have pa: inc (Vf (Vg (isf S) (J i j)) x) (Vg (isE S) j) by Wtac.
have pb: inc (Vf (Vg (isf S) (J i j)) y) (Vg (isE S) j) by Wtac.
apply/(ex7_eqv_prop2 jI); split => //.
by rewrite (inl_class_of_fij leij xE)  (inl_class_of_fij leij yE).
Qed.

Definition ex7_Ei i := quotient (ex7_eqv i).
Definition ex7_fij i j:=
  fun_on_quotients (ex7_eqv i) (ex7_eqv j) (Vg (isf S) (J i j)).


Lemma ex7_fij_prop1 i j: gle (isr S) i j ->
   function_prop (ex7_fij i j) (ex7_Ei i) (ex7_Ei j).
Proof.
move => lij; split.
- move:(inl_prop0 lij) => [iI jI].
  move:(ex7_eqv_prop1 iI) (ex7_eqv_prop1 jI) => [ha hb ][hc hd].
  move: (inl_prop4 lij) => [fij sij tij].
  have tij': target (Vg (isf S) (J i j)) = substrate (ex7_eqv j) by ue.
  have sij': source (Vg (isf S) (J i j)) = substrate (ex7_eqv i) by ue.
  by apply:foqcs_f.
- by rewrite /ex7_fij /fun_on_quotients /section_canon_proj; aw.
- by rewrite /ex7_fij /fun_on_quotients; aw.
Qed. 

Lemma ex7_fij_ev i j x: gle (isr S) i j -> inc x (ex7_Ei i) ->
    Vf (ex7_fij i j) x =  class (ex7_eqv j) (Vf (Vg (isf S) (J i j)) (rep x)).
Proof.
move => lij xE; move:(inl_prop0 lij) => [iI jI].
move:(ex7_eqv_prop1 iI) (ex7_eqv_prop1 jI) => [ha hb ][hc hd].
move: (inl_prop4 lij) => [fij sij tij].
rewrite /ex7_fij foqcs_V //; ue.
Qed.


Lemma ex7_fij_ev_bis i j x: gle (isr S) i j -> inc x (Vg (isE S) i) ->
     Vf (ex7_fij i j) (class (ex7_eqv i) x) =
    class (ex7_eqv j) (Vf (Vg (isf S) (J i j)) x).
Proof.
move => lij xE; move:(inl_prop0 lij) => [iI jI].
move:(ex7_eqv_prop1 iI) (ex7_eqv_prop1 jI) => [ha hb ][hc hd].
have cq:inc (class (ex7_eqv i) x) (ex7_Ei i) by apply: inc_class_setQ; ue.
have xe': inc x (substrate (ex7_eqv i)) by ue.
move: (related_rep_class ha xe')=> /(ex7_eqv_prop2 iI) [ra rb rc].
move: (inl_prop4 lij) => [fij sij tij]; rewrite (ex7_fij_ev lij cq).
suff: (related (ex7_eqv j)
               (Vf (Vg (isf S) (J i j)) (rep (class (ex7_eqv i) x)))
     (Vf (Vg (isf S) (J i j)) x)).
  by case/(related_equiv_P hc). 
apply/(ex7_eqv_prop2 jI); split => //; try Wtac.
rewrite inl_class_of_fij // - rc inl_class_of_fij //.
Qed.

  
Lemma ex7_fij_prop2 i: inc i (isI S) ->
   (ex7_fij i i) = identity (ex7_Ei i).
Proof.
move => iI.
move: (inl_prop1 iI) => lii.
apply: (identity_prop0 (ex7_fij_prop1 lii)) => x xEi.
move:(ex7_eqv_prop1 iI) => [eqRi sRi].
move: (rep_i_sr eqRi xEi); rewrite sRi => rE.
rewrite (ex7_fij_ev lii xEi) (is_identity_f iI) idV//.
by apply: class_rep.
Qed.


Lemma ex7_fij_prop3 i j k: gle (isr S) i j -> gle (isr S) j k ->
   ex7_fij j k \co ex7_fij i j = ex7_fij i k.
Proof.
move => lij ljk.
move:(proj33(is_preorder_r S) _ _ _ lij ljk) => lik.
move:(ex7_fij_prop1 lij) => [fij sij tij].
move:(ex7_fij_prop1 lik) => [fik sik tik].
move:(ex7_fij_prop1 ljk) => [fjk sjk tjk].
have co: ex7_fij j k \coP ex7_fij i j by split => //;ue.
apply: function_exten; aw=> //; try ue; first by fct_tac.
rewrite sij => x xEi.
have ha: inc x (source (ex7_fij i j)) by ue.
have hb: inc (Vf (ex7_fij i j) x) (ex7_Ei j) by Wtac.
rewrite compfV //.
rewrite (ex7_fij_ev lik xEi)(ex7_fij_ev ljk hb)(ex7_fij_ev lij xEi).
clear fij sij tij fik sik tik fjk sjk tjk ha hb co.
move:(inl_prop0 lij)(inl_prop0 ljk) => [iI jI][_ kI].
move:(ex7_eqv_prop1 iI) => [eqRi sRi].
move:(ex7_eqv_prop1 jI) => [eqRj sRj].
move:(ex7_eqv_prop1 kI) => [eqRk sRk].
move: (rep_i_sr eqRi xEi); rewrite sRi => rE.
move:(inl_prop4 lij) => [fij sij tij].
move:(inl_prop4 lik) => [fik sik tik].
move:(inl_prop4 ljk) => [fjk sjk tjk].
have fre: inc (Vf (Vg (isf S) (J i j)) (rep x)) (substrate (ex7_eqv j)).
  rewrite sRj; Wtac.
move: (related_rep_class eqRj fre); set y := rep (class _ _).
move/(ex7_eqv_prop2 jI) => [];set z := Vf _ _ => zEj yEj rzy.
apply:(class_eq1 eqRk); apply/(ex7_eqv_prop2 kI); split; try Wtac.
by rewrite inl_class_of_fij // inl_class_of_fij // - rzy /z inl_class_of_fij.
Qed.


Lemma ex7_fij_prop4 i j : gle (isr S) i j -> injection  (ex7_fij i j).
Proof.
move => lij.
move: (inl_prop0 lij) => [iI jI].
move:(ex7_eqv_prop1 iI) (ex7_eqv_prop1 jI)=> [eqRi sRi][eqRj sRj].
move: (inl_prop4 lij) => [fij sij tij].
move: (ex7_fij_prop1 lij) => [fij' sij' tij']; split => //; rewrite sij'.
move => x y xE yE; rewrite /= (ex7_fij_ev lij xE) (ex7_fij_ev lij yE) => eq1.
move:(rep_i_sr eqRi xE); rewrite sRi => rxE.
move:(rep_i_sr eqRi yE); rewrite sRi => ryE.
have ha: inc (Vf (Vg (isf S) (J i j)) (rep x)) (substrate (ex7_eqv j)).
  rewrite sRj; Wtac.
have hb: inc (Vf (Vg (isf S) (J i j)) (rep y)) (substrate (ex7_eqv j)).
  rewrite sRj; Wtac.
move /(related_equiv_P eqRj): (And3 ha hb eq1) =>  /(ex7_eqv_prop2 jI).
move => [_ _]; rewrite inl_class_of_fij //  inl_class_of_fij // => cc.
rewrite -(class_rep eqRi xE) -(class_rep eqRi yE). apply:(class_eq1 eqRi).
by apply/(ex7_eqv_prop2 iI). 
Qed.

  
Definition ex7_Ei_fam := Lg (isI S) ex7_Ei.
Definition ex7_fij_fam := Lg (isr S) (fun ij => ex7_fij (P ij) (Q ij)).

Lemma ex7_fij_prop1' p: inc p (isr S) ->
   function_prop (Vg ex7_fij_fam p) (Vg ex7_Ei_fam (P p)) (Vg ex7_Ei_fam (Q p)).
Proof.
move => pr.
move: (pr1_sr pr)(pr2_sr pr); rewrite is_substrate_r => ha hb.
move:(proj31 (is_preorder_r S) _ pr) => pp.
rewrite / ex7_fij_fam/ex7_Ei_fam ! LgV//.
by apply:ex7_fij_prop1; rewrite /gle/related pp.
Qed.

Definition ex7_system: inductive_system.
Proof.
apply (@InductiveSystem ex7_Ei_fam (isI S) (isr S) ex7_fij_fam).
- exact (is_preorder_r S).
- exact (is_substrate_r S).
- exact (@is_directed_r S).
- rewrite/ex7_Ei_fam; fprops.
- by rewrite/ex7_Ei_fam; aw.
- rewrite/ex7_fij_fam; fprops.
- by rewrite/ex7_fij_fam; aw.
- apply:ex7_fij_prop1'.
- move => i j k lij ljk; move:(proj33(is_preorder_r S) _ _ _ lij ljk) => lik.
  rewrite /ex7_fij_fam !LgV //; aw; apply:ex7_fij_prop3 => //.
- move=> i iI; move: (inl_prop1 iI) => lii.
  by rewrite /ex7_Ei_fam /ex7_fij_fam !LgV//; aw; apply:ex7_fij_prop2.
Defined.

Lemma ex7_system_val: inductive_system_on ex7_system
  ex7_Ei_fam (isI S) (isr S) ex7_fij_fam.
Proof.  by []. Qed.

Definition ex7_fct x :=
  class (inl_equiv S) (J (rep (P (rep x))) (Q (rep x))).
Definition  ex7_iso :=
  Lf ex7_fct (inductive_limit ex7_system) (inductive_limit S).


Lemma ex7_can_val_bj :
  bijection_prop ex7_iso (inductive_limit ex7_system) (inductive_limit S).
Proof.
rewrite/ex7_iso ; saw; apply: lf_bijective.
- move => x /inductive_limit_hi /= [ha hb _]; apply: inl_class_in_lim => //.
  move: (ex7_eqv_prop1 ha) => [eqv sr].
  by move: hb; rewrite/ex7_Ei_fam/ex7_Ei; rewrite LgV//; move/(rep_i_sr eqv); rewrite sr.
- move => x y /inductive_limit_hi /= [iI Px {2} ->].
  move => /inductive_limit_hi /= [jI Py {2} ->].
  move: (ex7_eqv_prop1 iI) => [eqvi sri].
  move: (ex7_eqv_prop1 jI) => [eqvj srj].
  move:Px Py; rewrite /ex7_Ei_fam; rewrite!LgV// => Px Py.
  rewrite - (class_rep eqvi Px) -(class_rep  eqvj Py) /ex7_fct.
  move:(rep_i_sr eqvi Px)(rep_i_sr eqvj Py); rewrite sri srj.
  set i := Q (rep x); set j := Q (rep y).
  set x' := rep _; set y' := rep (P (rep y)).
  move => xE yE /(inl_class_eq_bis iI jI xE yE) [k[]]; aw => lik ljk sv.
  have x'':inc (class (ex7_eqv i) x') (ex7_Ei i) by  apply:inc_class_setQ; ue.
  have y'':inc (class (ex7_eqv j) y') (ex7_Ei j) by  apply:inc_class_setQ; ue.
  have xE': inc (class (ex7_eqv i) x') (Vg (isE ex7_system) i).
    rewrite/= /ex7_Ei_fam; rewrite LgV//.
  have yE': inc (class (ex7_eqv j) y') (Vg (isE ex7_system) j).
    rewrite/= /ex7_Ei_fam; rewrite LgV//.
  apply/inl_class_eq_bis => //; exists k; aw; simpl; split => //.
  rewrite /ex7_fij_fam !LgV//; aw.
  by rewrite (ex7_fij_ev_bis lik xE) (ex7_fij_ev_bis ljk yE) sv.
move => y /inductive_limit_hi [Qx Px ->]; move:Px Qx.
set i := Q _; set x := P _; move => xE iI .
move:(ex7_eqv_prop1 iI) => [ha hb].
set t := class (ex7_eqv i) x.
have tE: inc t (ex7_Ei i) by apply: inc_class_setQ; ue.
exists (class (inl_equiv ex7_system) (J t i)). 
  apply:(inl_class_in_lim) => //=; rewrite/ex7_Ei_fam; rewrite LgV//.
have tEi: inc t (Vg (isE ex7_system) i) by rewrite /= /ex7_Ei_fam LgV.
have [eqv seqv]:= (inl_equiv_esr ex7_system).
have jti_s: inc (J t i) (substrate (inl_equiv ex7_system)).
  rewrite seqv; apply/inl_sumP; aw; split; fprops.
move: (related_rep_class eqv jti_s).
rewrite /ex7_fct; move/graph_on_P1 => [_ /inl_sumP /= [ {4} <-]].
set i' := Q _; set t' := P _ => iI' tEi';move => [k  []] /=; aw => lik lik'.
have tE':inc t' (ex7_Ei i') by move: tEi'; rewrite/ex7_Ei_fam; rewrite LgV.
move: (ex7_eqv_prop1 iI') => [eqi' sri'].
move: (rep_i_sr eqi' tE'); rewrite sri' => rt'E.
rewrite /ex7_fij_fam !LgV//;aw.
rewrite /t (ex7_fij_ev_bis lik xE)(ex7_fij_ev lik' tE') => eq1.
have kI := (proj2(inl_prop0 lik)).
move: (ex7_eqv_prop1 kI) => [eqk srk].
move: (inl_prop4 lik) => [fik sik tik].
move: (inl_prop4 lik') => [fik' sik' tik'].
have hc: inc (Vf (Vg (isf S) (J i k)) x) (substrate (ex7_eqv k))
  by rewrite srk; Wtac.
have hd:inc (Vf (Vg (isf S) (J i' k)) (rep t')) (substrate (ex7_eqv k)).
  by rewrite srk; Wtac.
move/(related_equiv_P eqk):(And3 hc hd eq1).
move/(ex7_eqv_prop2 kI)=> [_ _].
rewrite inl_class_of_fij // inl_class_of_fij //.
Qed.



End Exercise7.

  
Section Exercise8.

Variables S S': inductive_system.
Variable (u:Set).  
Hypothesis same_I: (inl_same_index S S').
Hypothesis (Hu: inl_map2_compat S S' u).

Lemma ex8_inl_subfm_hyp (S'' := inl_system_product same_I):
  inl_subfam_hyp S'' (Lg (isI S) (fun i => graph (Vg u i))).
Proof.
move:(inl_system_product_prop same_I); rewrite -/S'' => -[ha hb hc hd].
have pr1 j:  inc j (isI S) ->
  sub (graph (Vg u j)) (Vg (isE S) j \times Vg (isE S') j).
  move => iI.
  by move: Hu=> [_ _ hu _];move: (hu _ iI) => [[[ _ qa] _ _ ] <- <-].
rewrite /inl_subfam_hyp; split; aww.
  rewrite hb ha; move => i iI; rewrite /inl_product_E !LgV//; exact:pr1.
rewrite hc hd.
move => i j lij t.
move: (inl_prop0 lij) => [iI jI].
rewrite /inl_product_f !LgV//.
move: (Hu) =>[ _ _ _ h]; move:(h _ _ lij) => cc {h}.
move: (inl_prop4 lij) => [fij sij tij].
rewrite same_I in lij.
move: (inl_prop4 lij) => [fij' sij' tij'].
set f := _ \ftimes _.
have ff: function f by apply: ext_to_prod_f.
have sf: source f = (Vg (isE S) i \times Vg (isE S') i).
  by rewrite /f/ext_to_prod; aw; rewrite  sij sij'; aw.
have pr2: sub (graph (Vg u i)) (source f) by rewrite sf; exact: pr1.
move/(Vf_image_P ff pr2) => [w wg ->].
rewrite /f ext_to_prod_V2 //;last by rewrite sij sij' - sf;  apply: pr2.
move: Hu=> [_ _ hu _];move: (hu _ jI) => [fuj suj tuj].
move: (hu _ iI) => [fui sui tui].
move: (Vf_pr2 fui wg) (p1graph_source1 fui wg)  => qv pws.
have pws': inc (P w) (Vg (isE S) i).
  rewrite - sui; exact:  (p1graph_source1 fui wg).
set x := (Vf (Vg (isf S) (J i j)) (P w)).
have xsj: inc x (source (Vg u j)) by rewrite suj /x - tij; Wtac. 
move: (Vf_pr3 fuj xsj).
have -> //: (Vf (Vg u j) x) = (Vf (Vg (isf S') (J i j)) (Q w)).
have co1:  Vg (isf S') (J i j) \coP Vg u i by split => //;rewrite sij'.
have co2:  Vg u j \coP Vg (isf S) (J i j) by split => //; ue.
rewrite /x qv.
move/(f_equal (Vf ^~(P w))):cc; rewrite ! compfV//; ue.
Qed.
  
Definition ex8limit_graphs := inductive_system_subsets ex8_inl_subfm_hyp.
Definition ex8_graphs_limit := graph (inductive_limit_fun S S' u).

Lemma ex8limit_graphs_prop t (i := (Q (rep (P t)))) (x := (P (rep (P t)))):
  inc t ex8_graphs_limit ->
  [/\ inc i (isI S), inc x (Vg (isE S) i) &
        t = J (class (inl_equiv S) (J x i))
              (class (inl_equiv S') (J (Vf (Vg u i) x) i))].
Proof.
move: (inl_map2_prop same_I Hu).
rewrite /ex8_graphs_limit; set f := inductive_limit_fun _ _ _.
move => [[ff sf tf] _] tgf.
rewrite -(function_sgraph ff tgf).
move:(p1graph_source1 ff tgf) (Vf_pr2 ff tgf).
rewrite sf  => /inductive_limit_hi [iI xE ->] ->.
have iI' : inc i (isI S') by rewrite - (inl_same_index_same_I same_I).
by rewrite  (inl_map_val_aux2 same_I Hu iI xE). 
Qed.

Definition ex8_gl_val t := 
  let i := (Q (rep (P t))) in let x := (P (rep (P t))) in
  class (inl_equiv ex8limit_graphs) (J (J x (Vf (Vg u i) x)) i).


Lemma ex8_gl_val_ax:
  lf_axiom ex8_gl_val ex8_graphs_limit (inductive_limit ex8limit_graphs).
Proof.
move => t / ex8limit_graphs_prop.
rewrite /ex8_gl_val.
set i :=  (Q (rep (P t))); set x := (P (rep (P t))).
move => [iI xE _]; apply:inl_class_in_lim => //=; rewrite LgV//.
move: (proj43 Hu _ iI) => [fui sui tui];apply: Vf_pr3 => //; ue.
Qed.
  

Lemma  ex8_gl_val_bf (E := (inductive_limit ex8limit_graphs))
       (f:= Lf ex8_gl_val ex8_graphs_limit  E):
  bijection_prop f ex8_graphs_limit  E.
Proof.
have ax:= ex8_gl_val_ax.
rewrite /f;saw.
case:(inl_map2_prop same_I Hu); set fp := (inductive_limit_fun S S' u).
  move => [fff sff tff] ffp.
move:(inl_subfam_prop1 ex8_inl_subfm_hyp).
set g := inl_subfam_fct  _ _; set S'':= (inl_system_product same_I).
move => [gp1 gp2 gp3 gp4 gp5].
have Ha i k x : gle (isr S) i k -> inc x (Vg (isE S) i) ->
  Vf (Vg (isf S'') (J i k)) (J x (Vf (Vg u i) x)) =
  J (Vf (Vg (isf S) (J i k)) x) (Vf (Vg (isf S') (J i k)) (Vf (Vg u i) x)).
  move => ha hb;rewrite /= /(inl_product_f); rewrite LgV//.
  move:(inl_prop4 ha) =>[fa sa ta].
  have xs1:inc x (source (Vg (isf S) (J i k))) by ue.
  move:(proj1(inl_prop0 ha)) => iI.
  rewrite same_I in ha.
  move:(inl_prop4 ha) =>[fa' sa' ta'].
  have xs2: inc (Vf (Vg u i) x) (source (Vg (isf S') (J i k))).
  move: (proj43 Hu _ iI) => [fui sui tui]; rewrite sa'; Wtac.
  by rewrite ext_to_prod_V.
apply: (lf_bijective ax).
  move => t t' /ex8limit_graphs_prop [].
  set i := Q _; set x := P _ => iI xE eq1.
  move => /ex8limit_graphs_prop [].
  set i' := Q _; set x' := P _ => iI' xE' eq2.
  rewrite /ex8_gl_val -/i -/i' -/x -/x'.
  move: (proj43 Hu _ iI) => [fui sui tui].
  move: (proj43 Hu _ iI') => [fui' sui' tui'].
  have ha: inc (J x (Vf (Vg u i) x))
      (Vg (Lg (isI S) (fun z => graph (Vg u z))) i).
    by rewrite LgV//; apply: Vf_pr3 => //; ue.
   have hb: inc (J x' (Vf (Vg u i') x'))
      (Vg (Lg (isI S) (fun z => graph (Vg u z))) i').
    by rewrite LgV//; apply: Vf_pr3 => //; ue.
  move/(inl_class_eq_bis) => /= ww; move: (ww iI iI' ha hb).
  move => [k []]; aw; simpl. move => lik lik'.
  rewrite -/g gp2 // gp2 // Ha // Ha // => eq3.
  move:(pr1_def eq3) (pr2_def eq3) => eq4 eq5.
  rewrite eq1 eq2; congr J.
    by rewrite -(inl_class_of_fij lik xE) eq4 (inl_class_of_fij lik' xE').
  have hc: inc (Vf (Vg u i) x) (Vg (isE S') i) by Wtac.
  have hd:inc (Vf (Vg u i') x') (Vg (isE S') i') by  Wtac.
  rewrite same_I in lik lik'.
  by rewrite -(inl_class_of_fij lik hc)  eq5 - (inl_class_of_fij lik' hd).
move => y /inductive_limit_hi; set i := Q _ ; set x := P _; simpl.
move => [iI]; rewrite !LgV// => yg ->.
move: (proj43 Hu _ iI) => [fui sui tui].
move:(in_graph_Vf fui yg) => xv.
move:(p1graph_source1 fui yg) (p2graph_target1 fui yg);rewrite sui tui=> xE XE'.
set c1 := class (inl_equiv S) (J (P x) i).
have c1l: inc c1 (inductive_limit S).
  by apply: inl_class_in_lim.
set c2 := class (inl_equiv S') (J (Vf (Vg u i) (P x)) i).
have c2v:  c2 = Vf fp c1 by rewrite inl_map_val_aux2.
have zl:inc (J c1 c2) ex8_graphs_limit.
  rewrite /ex8_graphs_limit c2v; apply: Vf_pr3 => //; ue.
ex_tac.
move/inductive_limit_hi:c1l;
set j := Q (rep c1); set z := P (rep c1); move => [jI zE qc].
rewrite /ex8_gl_val; aw; rewrite -/j -/z.
move: (proj43 Hu _ jI) => [fuj suj tuj].
have ha: inc (J z (Vf (Vg u j) z)) (graph (Vg u j)).
   by apply: Vf_pr3 => //; ue.
have hb: inc (J (P x) (Vf (Vg u i) (P x))) (graph (Vg u i)) by rewrite - xv. 
apply/inl_class_eq_bis=> //.
    simpl; rewrite LgV//.
  by simpl; rewrite LgV//; apply: Vf_pr3 => //; ue.
move: qc; rewrite /c1.
move/(inl_class_eq_bis iI jI xE zE) => [k []]; aw => lik ljk sv.
exists k; saw.
rewrite xv; rewrite gp2 //; last by rewrite LgV.
rewrite gp2 //; last by rewrite LgV.
rewrite Ha // Ha//.
rewrite (inl_map2_compat_prop0 same_I Hu xE lik).
by rewrite (inl_map2_compat_prop0 same_I Hu zE ljk) sv.
Qed.




End Exercise8.




Section Exercise9.

Variables (E I r f: Set).
Hypothesis (or: preorder r) (sr:  substrate r = I)
  (fgE:fgraph E) (dE: domain E = I) 
  (fgf: fgraph f) (df: domain f = r) 
  (function_f:
    forall p, inc p r ->
              function_prop (Vg f p) (Vg E (P p)) (Vg E (Q p)))
  (compose_f: forall i  j k, gle r i j -> gle r j k ->
                  Vg f (J j k) \co  Vg f (J i j) = Vg f (J i k))
  (identity_f: forall i, inc i I -> Vg  f (J i i) = identity (Vg E i)).


Definition ex9_G := disjointU E.


Lemma ex9G_P x: inc x ex9_G <->
  [/\ pairp x, inc (Q x) I & inc (P x) (Vg E (Q x))].
Proof.
split; first by case/disjointU_P; rewrite dE. 
by move => [ha hb hc]; apply /disjointU_P; rewrite dE. 
Qed.

Definition ex9_rel x y:=
  gle r (Q x) (Q y) /\ P y = Vf (Vg f (J (Q x) (Q y))) (P x).


Definition ex9_srel x y := 
   exists k, [/\ gle r (Q x) k,  gle r (Q y) k &
   Vf (Vg f (J (Q x) k)) (P x) =  Vf (Vg f (J (Q y) k)) (P y) ].

Lemma ex9_propa x y: inc x ex9_G -> inc y ex9_G ->
  ex9_rel x y -> ex9_srel x y.
Proof.
move => /ex9G_P [px Px Qx] /ex9G_P [py Py Qy] [qa qb].
have: gle r (Q y) (Q y) by  apply: (proj32 or); rewrite sr.
by exists (Q y); split => //; rewrite - qb (identity_f Py) idV.
Qed.


Definition ex9_rels x y:=
  [/\ inc x ex9_G, inc y ex9_G & ex9_rel x y \/  ex9_rel y x].

Lemma  ex9_propb: reflexive_re  ex9_rels ex9_G.
Proof.
move => x; split.
  move => h; split => //; left.
  move/ex9G_P: h => [px Qx Px].
  have g: gle r (Q x) (Q x) by  apply: (proj32 or); rewrite sr.
  by split => //; rewrite  (identity_f Qx) idV.
by case.
Qed.

Lemma ex9_propc: symmetric_r  ex9_rels. 
Proof.
by move => x y [ha hb hc]; split => //; case: hc => h; [right  | left].
Qed.

Lemma ex9_propd: (forall x y, ex9_rels x y -> inc x ex9_G). 
Proof. by move=> x y; case. Qed.

Definition ex9_rels_ext := chain_equivalence ex9_rels ex9_G.

Lemma chain_equivalence_eq: equivalence_on ex9_rels_ext ex9_G.
Proof.
apply:(chain_equivalence_eq ex9_propb ex9_propc ex9_propd). 
Qed.

Lemma ex9_rels_ext_minimal: 
  ex9_rels_ext  = eqv_smallest  ex9_G  ex9_rels.
Proof.
exact (chain_equivalence_is_smallest  ex9_propb ex9_propc ex9_propd).
Qed.

Lemma ex9_prope: sub (graph_on ex9_srel ex9_G) ex9_rels_ext.
Proof.
move => t /Zo_P [/setX_P[pp Px Qx] [k [leij lejk ff]]].
move:(arg2_sr leij); rewrite sr => kI.
move/ex9G_P:(Px) => [ppx Ppx Qpx].
move/ex9G_P:(Qx) => [pqx Pqx Qqx].
rewrite - pp.
apply/graph_on_P1; split => //.
set z :=  J (Vf (Vg f (J (Q (P t)) k)) (P (P t))) k.
have zg: inc z ex9_G.
  rewrite /z;apply/ex9G_P; split;aww.
  case:(function_f leij); aw => fa sa ta;  Wtac. 
exists (chain_next (P t) (chain_pair z (Q t))); split => //=; split.
  split => //; left; rewrite /z; saw.
  split => //; right; rewrite /z ff; saw.
Qed.


Lemma ex9_propf:
  right_directed_on r I -> equivalence_on (graph_on ex9_srel ex9_G) ex9_G.
Proof.
move => h.
set S := InductiveSystem or sr h fgE dE fgf df function_f compose_f identity_f.
by move: (inl_equiv_esr S) => [ha hb].
Qed.

  
Lemma ex9_rels_special:
  right_directed_on r I -> 
  ex9_rels_ext = graph_on  ex9_srel ex9_G. 
Proof.
move => / ex9_propf ha.
set s := (graph_on ex9_srel ex9_G).
apply: extensionality; last by apply:ex9_prope.
set T:= (Zo (equivalences ex9_G) (eqv_smaller ex9_rels)).
have sT: inc s T.
  apply/Zo_P; split; first by apply/equivalencesP.
  move => x y; move =>[xG yG ll]; case: ll => ll1.
    by apply/graph_on_P1; split => //; apply:ex9_propa.
  by apply:(proj44 (proj1 ha));apply/graph_on_P1; split=> //; apply:ex9_propa.
rewrite ex9_rels_ext_minimal => t xt; exact:(setI_hi xt sT).
Qed.

Definition ex9_quo := quotient ex9_rels_ext.

Lemma ex9_quoP x: inc x ex9_quo <-> classp ex9_rels_ext x.
Proof.
exact:(setQ_P (proj1 (chain_equivalence_eq))).
Qed.

Lemma ex9_propg (h: right_directed_on r I)
  (S := InductiveSystem or sr h fgE dE fgf df function_f compose_f identity_f):
  ex9_quo = inductive_limit S.
Proof.
move:(ex9_rels_special h) => eqxx.
set_extens t.
  by move/ex9_quoP; rewrite eqxx => w; apply/inductive_limitP. 
by move/inductive_limitP => w;apply/ex9_quoP; rewrite eqxx. 
Qed.

Definition ex9_can_fun i :=
  Lf (fun x => class  ex9_rels_ext (J x i)) (Vg E i) ex9_quo.


Lemma ex9_can_fun_ax i: inc i I  ->
   lf_axiom (fun x => class ex9_rels_ext (J x i)) (Vg E i) ex9_quo.
Proof.
move: (chain_equivalence_eq) => [ha hb].
move => uI x xE;  apply/ex9_quoP; apply: (class_class ha); rewrite hb.
apply/ ex9G_P; split; aww.
Qed.

Lemma ex9_can_fun_fp i: inc i I ->
     function_prop (ex9_can_fun i) (Vg E i)  ex9_quo.
Proof.
move => iI; rewrite /ex9_can_fun; saw; apply: lf_function.
exact:(ex9_can_fun_ax iI).
Qed.                     

Variables (u F: Set).

Hypotheses 
  (fgu:fgraph u)
  (du: domain u = I)
  (function_u: forall i, inc i I -> function_prop (Vg u i) (Vg E i) F)
  (compose_u: forall i j, gle r i j -> (Vg u j) \co Vg f (J i j) = Vg u i).

Definition ex9_map_property  g:=
  function_prop g ex9_quo F /\
  forall i, inc i I -> (Vg u i) = g \co (ex9_can_fun i).



Lemma ex9_map_property_res1 g i x:
  ex9_map_property g ->
  inc i I -> inc x (Vg E i) ->
  Vf g (class ex9_rels_ext (J x i)) = Vf (Vg u i) x.
Proof.
move =>[[fg sg tg] hb] hc hd.
move:(ex9_can_fun_fp hc) => [fc sc tc].
have co: g \coP ex9_can_fun i by split => //; ue.
have xs: inc x (source (ex9_can_fun i)) by ue.
rewrite (hb _ hc) compfV//.
by rewrite /ex9_can_fun LfV//; apply: ex9_can_fun_ax.
Qed.


Lemma ex9_map_unique g g':
  ex9_map_property g -> ex9_map_property g' -> g = g'.
Proof.
move => hb hc.
move:(proj1 hb) (proj1 hc) => [fg sg tg] [fg' sg' tg'].
apply: function_exten => //; try ue.
move: (chain_equivalence_eq) => [eqv seq].
rewrite sg => x /ex9_quoP [rs ->].
move: rs; rewrite seq => /ex9G_P [pr p1 p2]. 
rewrite - pr.
by  rewrite (ex9_map_property_res1 hb p1 p2) (ex9_map_property_res1 hc p1 p2).
Qed.



Definition ex9_map_val := fun y => Vf (Vg u (Q (rep y))) (P (rep y)).
Definition ex9_map :=  Lf ex9_map_val ex9_quo F.
  
Lemma ex9_map_ax : lf_axiom  ex9_map_val ex9_quo F.
Proof.
move: (chain_equivalence_eq) => [eqv seq].
move => x /ex9_quoP []; rewrite seq; move/ex9G_P =>[pr Qr Pr] _.
move: (function_u Qr) => [fu su tu].
rewrite /ex9_map_val; Wtac.
Qed.

Lemma ex9_map_aux x y: related ex9_rels_ext x y  ->
  Vf (Vg u (Q x)) (P x) = Vf (Vg u (Q y)) (P y).
Proof.
have Ha a b: inc a ex9_G -> inc b ex9_G -> ex9_rel a b ->
   Vf (Vg u (Q a)) (P a) = Vf (Vg u (Q b)) (P b).
  move => /ex9G_P [pa aI aE] /ex9G_P [pb bI bE] [leij ->].
  case:(function_f leij); aw => fij sij tij.
  move:(function_u bI) => [fu su tu].
  have ax1: Vg u (Q b) \coP Vg f (J (Q a) (Q b)) by split => //; ue.
  have pas: inc (P a) (source (Vg f (J (Q a) (Q b)))) by ue.
  rewrite - (compose_u leij) compfV//.
have H a b:  ex9_rels a b -> Vf (Vg u (Q a)) (P a) = Vf (Vg u (Q b)) (P b).
  move => [aG bG]; case => h1;[ by apply Ha | by symmetry; apply: Ha].
move/graph_on_P1 => [ _ _ [c [cc <- <-]]] {x y}.
elim:c cc; first by move => x y /=; apply: H.
by move => x c Hr /= [qa qb]; rewrite (H _ _ qa); apply: Hr.
Qed.


Lemma ex9_map_prop: ex9_map_property ex9_map.
Proof.
move:ex9_map_ax => ax.
have ra:function_prop ex9_map ex9_quo F.
  by rewrite /ex9_map; saw; apply: lf_function.
split => // i iI.
move: ra (function_u iI) => [fa sa ta] [fb sb tb].
move:(ex9_can_fun_fp iI) => [fc sc tc].
move: (chain_equivalence_eq) => [eqv seq].
have cc: ex9_map \coP ex9_can_fun i by split; fprops; ue.
apply: function_exten => //; aw; try ue; first by apply:compf_f.
rewrite sb => x xEi; rewrite compfV//; last by ue.
have xiE: inc (J x i) ex9_G by apply/ex9G_P;split; aww.
have ha:inc (Vf (ex9_can_fun i) x) ex9_quo by Wtac.
have ax1:= ex9_can_fun_ax iI.
rewrite /ex9_map/ex9_map_val LfV //.
move: ha;rewrite /ex9_can_fun; rewrite !LfV//.
case/ex9_quoP; set y := rep _ => ys eq1.
have xiE': inc (J x i) (substrate ex9_rels_ext) by ue.
move/(related_equiv_P eqv): (And3 xiE' ys eq1).
by move/ex9_map_aux; aw.
Qed.

End Exercise9.


End Limits.
Export Limits.

