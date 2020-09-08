(** * Theory of Sets EIII-1 Order relations. Ordered sets 
  Copyright INRIA (2009-2013) Apics, Marelle Team (Jose Grimm).
*)

(* $Id: sset5.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)

Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Warnings "notation-overridden".
Require Export sset4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Border.

(* some usefule sets *)
Definition injections E F :=
  Zo (functions E F)(injection). 

Definition surjections  E F :=
  Zo (functions E F)(surjection). 

Definition partitions E :=
  Zo (\Po(\Po E)) (fun z => partition_s z E).

Definition fgraphs x y :=
  Zo (\Po (x \times y)) fgraph.


Lemma injectionsP E F f: inc f (injections E F) <-> injection_prop f E F.
Proof.
split; first by by move => /Zo_P [/functionsP [ha hb hc] hd].
move => [ha hb hc]; apply: Zo_i => //; apply/functionsP; split => //; fct_tac.
Qed.


Lemma surjectionsP E F f: inc f (surjections E F) <-> surjection_prop f E F.
Proof.
split; first by by move => /Zo_P [/functionsP [ha hb hc] hd].
move => [ha hb hc]; apply: Zo_i => //; apply/functionsP; split => //; fct_tac.
Qed.

Lemma partitionsP p E:
  inc p (partitions E) <-> partition_s p E.
Proof. 
split; [by move/Zo_hi|move => h;apply/Zo_i=> //;apply /setP_P => t ty ].
by move:h=> [[<- _] _ ]; apply/setP_P; apply: setU_s1.
Qed.

Lemma fgraphsP X Y f:
  inc f (fgraphs X Y) <-> [/\ fgraph f, sub (domain f) X & sub (range f ) Y]. 
Proof.
split.
  move=> /Zo_P [/setP_P ha hb].
  by split => // x /funI_P [ y /ha/setX_P[_ p q] -->].
move =>[ha hb hc]; apply: Zo_i => //; apply/setP_P => t tg.
apply /setX_P; split.
- exact: (proj1 ha _ tg).
- by apply: hb; apply: funI_i.
- by apply: hc; apply: funI_i.
Qed.



(** ** EIII-1-1 Definition of an order relation *)
(** Definitions are given in file sset4 *)

Lemma equality_order_r: order_r (fun x y => x = y).
Proof. split; first (by move => y x z -> ->); move => x y //. Qed.

Lemma sub_order_r: order_r sub.
Proof.
split. 
+ by move=> x y t xy yz; apply: (sub_trans xy yz).
+ by move=> x y xy yx; apply: extensionality. 
+ by move=> x y; split; apply: sub_refl. 
Qed.

(** The opposite of [r x y] is the relation [r y x]. 
    A symmetric relation is equal to its opposite. 
    The opposite of an order relation is an order relation *)

Definition opposite_relation (r:relation) :=  fun x y => r y x.

Lemma opposite_preorder_r r: preorder_r r -> preorder_r (opposite_relation r).
Proof. 
rewrite /preorder_r/opposite_relation; move => [tr rr]. 
split; [by move=> x y z xy yz; apply: tr yz xy | by move=> x y /rr [] ].
Qed.

Lemma opposite_order_r r:  order_r r -> order_r (opposite_relation r).
Proof.
move=> [tr ar rr].
move /opposite_preorder_r: (conj tr rr) => [tr' rr'].
by split => // x y xy yx; apply: (ar _  _ yx). 
Qed.

(** An order is the graph of an order relation *)

Lemma order_from_rel1 r x:
  transitive_r r ->
  (forall u v, inc u x -> inc v x -> r u v -> r v u -> u = v) ->
  (forall u, inc u x -> r u u) -> 
  order (graph_on r x).
Proof.
move=> tr sy re.
have ->: (graph_on r x = graph_on (fun a b => [/\ inc a x, inc b x & r a b]) x).
  by apply: Zo_exten1 => t /setX_P [_ px qx]; split => // [] [_ _].
apply: order_from_rel; split.
+ by move => a b c [ax bx rab] [_ cx rbc]; split => //; apply: tr rab rbc.
+ by move=> a b [ax bx rab] [_ cx rbc]; apply: sy.
+ by move=> a b [ax bx rab];split => //; split => //; apply: re.
Qed.


(** We define [gle r x y] and [glt r x y] *)

Definition gle r x y := related r x y.
Definition glt r x y := gle r x y /\ x <> y.

Lemma order_reflexivityP r: order r -> 
  forall a, (inc a (substrate r) <-> gle r a a).
Proof. 
move=> [_ or _ _]; rewrite /gle;split => h; [by apply: or | substr_tac].
Qed.

Lemma order_antisymmetry r a b:
  order r -> gle r a b -> gle r b a -> a = b.
Proof. move=> [_ _ _]; apply. Qed.

Lemma order_transitivity r a b c:
  order r -> gle r a b -> gle r b c -> gle r a c.
Proof. move=> [_ _ t _]; apply: t. Qed.

Lemma lt_leq_trans r x y z: 
  order r -> glt r x y -> gle r y z -> glt r x z.
Proof. 
move=> or [le1 nxy] le2; split; first by apply: order_transitivity le1 le2. 
dneg xz; rewrite -xz in le2.
apply: (order_antisymmetry or le1 le2).
Qed.

Lemma leq_lt_trans r x y z:
  order r -> gle r x y -> glt r y z -> glt r x z.
Proof. 
move=> or le1 [le2 nxy]; split; first by apply: order_transitivity le1 le2.
dneg xz; rewrite xz in le1.
apply: (order_antisymmetry or le2 le1).
Qed.

Lemma lt_lt_trans r a b c:
   order r -> glt r a b -> glt r b c -> glt r a c.
Proof. move=> or [le1 _] le2; apply: (leq_lt_trans or le1 le2). Qed.

Lemma not_le_gt r x y: order r -> gle r x y -> glt r y x -> False.
Proof. 
by move=> or le1 le2; move: (leq_lt_trans or le1 le2) => [_] []. 
Qed. 

Lemma order_exten r r': order r -> order r' ->
  (forall x y, gle r x y <-> gle r' x y) -> (r = r').
Proof. by move=> or or'; apply: sgraph_exten; fprops. Qed.


Lemma order_cp0  r r': order r -> order r' ->
  ((sub r r') <-> (forall x y, gle r x y -> gle r' x y)).
Proof.
move => or or'; split; first by move => h x y xy; apply: h.
move => h t tr.
move: ((proj41 or) _ tr) => p; move: tr; rewrite -p; apply:h.
Qed.

(** A tactic that uses properties of order *)

Ltac order_tac:=
  match goal with 
    | H1: gle ?r ?x _ |- inc ?x (substrate ?r)
      => exact: (arg1_sr H1)
    | H1: glt ?r ?x _ |- inc ?x (substrate ?r)
      => move: H1 => [H1 _] ; order_tac 
    | H1:gle ?r _ ?x |- inc ?x (substrate ?r) 
      => exact: (arg2_sr H1)
    | H1:glt ?r _ ?x |- inc ?x (substrate ?r) 
      => move: H1 => [H1 _]; order_tac 
    | H: order ?r, H1: inc ?u (substrate ?r) |- related ?r ?u ?u
      => apply /(order_reflexivityP H)
    | H: order ?r |- inc (J ?u ?u) ?r
       => apply /(order_reflexivityP H)
    | H: order ?r |- gle ?r ?u ?u
       =>  apply /(order_reflexivityP H)
    | H1: gle ?r ?x ?y, H2: gle ?r ?y ?x, H:order ?r |- 
        ?x = ?y => exact: (order_antisymmetry H H1 H2)
    | H:order ?r, H1:related ?r ?x ?y, H2: related ?r ?y ?x |- ?x = ?y
      => apply (order_antisymmetry H H1 H2)
    | H:order ?r, H1: inc (J ?x ?y) ?r , H2: inc (J ?y ?x) ?r |- ?x = ?y
      => apply (order_antisymmetry H H1 H2)
    | H:order ?r, H1:related ?r ?u ?v, H2: related ?r ?v ?w
      |- related ?r ?u ?w
      => apply (order_transitivity H H1 H2)
    | H:order ?r, H1:gle ?r ?u ?v, H2: gle ?r ?v ?w |- gle ?r ?u ?w
      => apply (order_transitivity H H1 H2)
    | H: order ?r, H1: inc (J ?u ?v) ?r, H2: inc (J ?v ?w) ?r |-
      inc (J ?u ?w) ?r
      => apply (order_transitivity H H1 H2)
    |  H1: gle ?r ?x ?y, H2: glt ?r ?y ?x, H: order ?r |- _
      => case: (not_le_gt H H1 H2) 
    | H1:glt ?r ?x ?y, H2: glt ?r ?y ?x, H:order ?r |- _
      => move: H1 => [H1 _] ; case: (not_le_gt H H1 H2) 
    | H1:order ?r, H2:glt ?r ?x ?y, H3: gle ?r ?y ?z |- glt ?r ?x ?z
       => exact: (lt_leq_trans H1 H2 H3)
    | H1:order ?r, H2:gle ?r ?x ?y, H3: glt ?r ?y ?z |- glt ?r ?x ?z
       => exact: (leq_lt_trans H1 H2 H3)
    | H1:order ?r, H2:glt ?r ?x ?y, H3: glt ?r ?y ?z |- glt ?r ?x ?z
       => exact: (lt_lt_trans H1 H2 H3)
    | H1:order ?r, H2:gle ?r ?x ?y |- glt ?r ?x ?y
       => split =>// 
    | H:glt ?r ?x ?y |- gle ?r ?x ?y
       => by move: H=> [] 
end.

(** The opposite of an order is the inverse graph *) 

Definition opp_order := inverse_graph.

Lemma opp_gleP r x y:  gle (opp_order r) x y <-> gle r y x.
Proof. exact: igraph_pP. Qed.

Lemma opp_gltP r x y:  glt (opp_order r) x y <-> glt r y x.
Proof. by split; move => [] /opp_gleP pa pb; split => //; dneg h. Qed.

Lemma opp_osr r: order r -> order_on  (opp_order r) (substrate r).
Proof.
move => osr.
have go: sgraph (opp_order r) by fprops.
have pc: substrate (opp_order r) = (substrate r).
  set_extens x.
    case/(substrate_P go) => [][y] /igraph_pP h; substr_tac.
  by move => xsr; apply /(arg1_sr (y:=x))/igraph_pP /(order_reflexivityP osr).
split => //;split; first by fprops.
    by move => t; rewrite pc => yg; apply/opp_gleP; order_tac.
  move => x y z /opp_gleP pa /opp_gleP pb; apply/opp_gleP; order_tac. 
move => x y  /opp_gleP pa /opp_gleP pb; order_tac.
Qed.

(** Inclusion order on the powerset of a set, or a part of it *)

Definition sub_order :=  graph_on sub.
Definition subp_order E := sub_order (\Po E).

Lemma sub_osr A: order_on (sub_order A) A.
Proof. 
split; first by apply: order_from_rel; apply: sub_order_r.
apply: graph_on_sr => x; fprops.
Qed.

Lemma subp_osr E: order_on (subp_order E) (\Po E).
Proof. exact: sub_osr. Qed.

Lemma sub_gleP A u v: 
  gle (sub_order A) u v <-> [/\ inc u A, inc v A & sub u v].
Proof. by apply /graph_on_P1. Qed.

Lemma subp_gleP E u v:
  gle (subp_order E) u v <-> [/\ sub u E, sub v E & sub u v].
Proof. 
split; first by move /graph_on_P1 => [] /setP_P pa /setP_P pb.
by move => [pa pb pc]; apply /graph_on_P1;split => //; apply/setP_P.
Qed.

(** Extension order on partial functions from [x] to [y] *)

Definition extension_order E F := 
  graph_on extends (sub_functions E F).

Lemma extension_osr E F: 
  order_on (extension_order E F) (sub_functions E F).
Proof.
split; last by apply: graph_on_sr => a /sfunctionsP [pa pb pc]; split; fprops.
apply: order_from_rel;split.
- move=> a b c [fa fb gba tba] [fc _ gcb tcb].
  split => //; [ by apply: sub_trans gba | by apply: sub_trans tba ].
- move=> a b [fb fa gba tba] [_ _ gab tab].
  have grab: graph a = graph b by apply: extensionality.
  have tgab: target a = target b by apply: extensionality.
  by apply: function_exten1. 
- move => a b [fa fb _ _ ]; split; split;fprops.
Qed.

Lemma extension_orderP E F f g:
  gle (extension_order E F) g f <->
  [/\ inc g (sub_functions E F), inc f (sub_functions E F)
    & extends g f].
Proof. apply /graph_on_P0. Qed.

Lemma extension_order_P1 E F f g:
  gle (extension_order E F) g f <-> 
  [/\ inc g (sub_functions E F), inc f (sub_functions E F)
    & sub (graph f) (graph g)].
Proof. 
split; first by move/extension_orderP => [pa pb [_ _ pd _]].
move=> [p1 p2 sh]; apply/extension_orderP; split=>//.
move: p1 p2 => /sfunctionsP [fg _ tg] /sfunctionsP [ff _ tf]. 
split => //; rewrite tg tf;fprops.
Qed.

Lemma extension_order_P2  E F f g:
  gle (opp_order (extension_order E F)) g f <->
  [/\ inc g (sub_functions E F), inc f (sub_functions E F)
    & sub (graph g) (graph f)].
Proof. 
split; first by move/opp_gleP /extension_order_P1=> []. 
by move => [pa pb pc]; apply/opp_gleP /extension_order_P1.
Qed.

Lemma extension_order_pr E F f g:
  gle (opp_order (extension_order E F)) f g ->
  {inc source f, f =1f g}.
Proof. 
move/opp_gleP/extension_orderP=> [gs fs et]; exact: (extends_sV et). 
Qed.

(** Example 4. Order between partitions on a set *)




Definition part_fun p E := canonical_injection p (\Po E).

Lemma partition_set_in_PP p E:
  partition_s p E -> inc p (\Po (\Po E)).
Proof. 
by move=> [[<- _] _ ]; apply /setP_P => t ty;apply/setP_P; apply: setU_s1.
Qed.

Lemma pfs_f p E: partition_s p E -> function (part_fun p E).
Proof. 
by move=> pa; apply: ci_f; apply/setP_P;apply: partition_set_in_PP.
Qed.

Lemma pfs_V p E a: partition_s p E -> inc a p -> Vf (part_fun p E) a = a.
Proof. 
by move => pa; apply: ci_V => //; apply/setP_P; apply: partition_set_in_PP.
Qed.

Lemma pfs_partition p E:
  partition_s p E ->  partition_w_fam (graph (part_fun p E)) E.
Proof.
move=> pa.
move: (pfs_f pa) => fpa.
move: (pa)=> [[ux di] _].
have Wp i: inc i p ->  Vg (graph (part_fun p E)) i = i.
  by move => iy; apply: pfs_V.
have dg: domain (graph (part_fun p E)) = p.
  by rewrite domain_fg // /part_fun /canonical_injection; aw.
split; fprops.
  by move=> i j; rewrite dg => iy jy; rewrite Wp // Wp //; apply: di. 
set_extens v => vs.
  move: (setUb_hi vs)=> [w]; rewrite dg.  
  move=> wy; rewrite Wp // -ux => vW; union_tac.
rewrite -ux in vs; move: (setU_hi vs) => [w vw wy].
by apply /setUb_P; exists w; rewrite ? dg ? (Wp _ wy). 
Qed.

(** The relation [coarser_cs] is an ordering on the set of partitions.
  We know the greatest and least element  *)

Definition coarser x := graph_on coarser_cs (partitions x).

Lemma coarser_gleP x y y':
  gle (coarser x) y y' <->
  [/\ partition_s y x, partition_s y' x & coarser_cs y y'].
Proof. 
split.
  by move/Zo_P => [/setXp_P [/partitionsP pa /partitionsP pb]]; aw.
move => [pa pb pc]; apply: Zo_i; last by aw.
by apply /setXp_P; split;apply /partitionsP.
Qed.

Lemma coarser_osr x: order_on (coarser x) (partitions x).
Proof.
have sr :substrate (coarser x) = partitions x.
  apply: extensionality; first by apply: graph_on_sr1.
  move => t ts.
  apply: (@arg1_sr _ t t); apply:Zo_i.
    by apply/setXp_P; split.
  aw; apply: coarserR.
split=> //;split.
- by apply: graph_on_graph.
- hnf; rewrite sr => y /partitionsP  h'.
  apply/coarser_gleP;split => //; apply: coarserR.
- move=> a b c /coarser_gleP [pa _ ab] /coarser_gleP [_ pb bc].
  apply /coarser_gleP;split => //;  apply: (coarserT ab bc).
- move=> a b /coarser_gleP [pa _ ab] /coarser_gleP [pb _ ba]. 
  apply: (coarserA pa pb ab ba).
Qed.

Lemma least_partition_is_least x y:
  nonempty x ->
  partition_s y x -> gle (coarser x) (least_partition x) y.
Proof. 
move=> nex pa;apply/coarser_gleP;split => //; first by apply:least_is_partition.
move=> u uy; rewrite /least_partition. 
by ex_tac; move:(partition_set_in_PP pa) => /setP_P yp; apply/setP_P; apply: yp.
Qed.

Lemma greatest_partition_is_greatest x y:
  partition_s y x -> gle (coarser x) y (greatest_partition x).
Proof. 
move=> pa; move: (pa) => [[pb _] _]; apply /coarser_gleP.
split => //; first by apply: greatest_is_partition. 
move=> u /funI_P [b bx ->].
by move: bx; rewrite -pb;move /setU_P=> [z bz zy];ex_tac; move=> t /set1_P ->.
Qed.

(** Assume that [y] is a partition of [x]; we deduce an equivalence on [x].
 The union of all [coarse a] for [a] in [y] is the graph of this equivalence
  *)

Definition partition_relset y x :=
  partition_relation (part_fun y x) x.

Lemma prs_is_equivalence y x:
  partition_s y x -> equivalence (partition_relset y x).
Proof. 
move=> pa; apply: isc_rel_equivalence; first by apply: pfs_f. 
by apply: pfs_partition.
Qed.

Definition partition_relset_aux y x := 
  Zo (\Po (coarse x)) (fun z => exists2 a, inc a y & z = coarse a).

Lemma partition_relset_pr1 y x a:
  partition_s y x -> 
  inc a y -> inc (coarse a) (partition_relset_aux y x).
Proof.
move=> pa ay.
move /setP_P: (partition_set_in_PP pa) => yp.
apply:Zo_i; last by ex_tac. 
by apply /setP_P; apply:setX_Sll; apply/setP_P; apply: yp.
Qed.

Lemma partition_relset_pr y x:
  partition_s y x -> 
  partition_relset y x = union (partition_relset_aux y x).
Proof. 
move=> pa.
have pfa: (partition_w_fam (graph(part_fun y x)) x) by apply: pfs_partition. 
have sp:source (part_fun y x) = y by rewrite /part_fun /canonical_injection;aw.
move: (partition_set_in_PP pa); aw => ypp.
have p1: function (part_fun y x) by apply: pfs_f.
have p2: partition_w_fam (graph (part_fun y x)) x.
  by move: (prs_is_equivalence pa); fprops.
have p3: sgraph (partition_relation (part_fun y x) x).
  by rewrite /partition_relation; apply: graph_on_graph.
have p4:sgraph (union (partition_relset_aux y x)).
  move=> t tp; move: (setU_hi tp); rewrite/partition_relset_aux.
  by move=> [z tz /Zo_P [] /setP_P zp _]; move: (zp _ tz) => /setX_P [].
apply: sgraph_exten => //. 
move=> u v; split.
  move /(isc_rel_P p1 p2); rewrite /in_same_coset sp.
  move=> [i [iy ]]; rewrite pfs_V // => ui vi.
  apply (@setU_i _ (coarse i)); first by apply: setXp_i.
  by apply: partition_relset_pr1. 
move/setU_P  => [z pz] /Zo_P  [zp [a ay zc]].
move: pz; rewrite zc; move /setXp_P => [ua va].
by apply/(isc_rel_P p1 p2); hnf;rewrite sp; exists a;split=> //; rewrite pfs_V.
Qed.

Lemma sub_part_relsetX y x:
  partition_s y x -> sub (partition_relset y x) (coarse x).
Proof. 
move=> pa; rewrite partition_relset_pr // => t tu.
by move: (setU_hi tu) => [z tz /Zo_P [/setP_P zp _ ]]; apply: zp.
Qed.

(** A partition [y] is coarser than [y] if [sub z' z] where [z] and [z'] are 
  the associated equivalence *)

Lemma partition_relset_order x y y':
  partition_s y x -> partition_s y' x -> 
  (sub (partition_relset y' x)(partition_relset y x) <->
    gle (coarser x) y y').
Proof. 
move=> pa pa'.
do 2 rewrite partition_relset_pr //.
split; last first.
  move /coarser_gleP=> [_ _ hyp] z /setU_hi [t zt /Zo_P [tp [a ay tc]]].
  have [b iby ab] := (hyp _ ay).
  apply: (@setU_i _ (coarse b)); first by apply (setX_Sll ab); ue.
  by apply: partition_relset_pr1. 
move => suu; apply/coarser_gleP;split=>// a ay.
have [b ba]:=(proj2 pa' _ ay).
have p: (forall u, inc u a ->  exists c, [/\ inc c y, inc b c& inc u c]).
  move=> u ua. 
  have q: (inc (J b u) (union (partition_relset_aux y' x))).
    apply: (@setU_i _ (coarse a)); first by apply:setXp_i.
    apply: (partition_relset_pr1 pa' ay).
  have [z Jbb /Zo_P [zp [c cy zc]]] := (setU_hi  (suu _ q)).
  by move: Jbb; rewrite zc; move/setXp_P=> [s1 s2]; exists c. 
move: (p _ ba) => [c [cy bc _]]; ex_tac => d /p [f [fy bf df]].
case: (proj2 (proj1 pa) _ _ cy fy); first by move => ->.
by move=> dcf; case: (nondisjoint bc bf dcf).
Qed.

Lemma part_relset_anti x y y':
  partition_s y x -> partition_s y' x -> 
  (partition_relset y' x = partition_relset y x) ->
   y = y'.
Proof. 
move: x y y'.
suff: (forall x y y',
  partition_s y x -> partition_s y' x -> 
  (partition_relset y' x = partition_relset y x) ->
  sub y y').
  move=> aux a b c p1 p2 eq; apply: extensionality.
     apply: aux p1 p2 eq.  
  apply: aux p2 p1 (sym_eq eq). 
move=> x y y' pa pa'.
rewrite (partition_relset_pr pa) (partition_relset_pr pa') => eq a ay.
have cpy:= (partition_relset_pr1 pa ay).
have [b ba] := (proj2 pa _ ay).
have p: (forall u v,inc u a -> inc v a ->  
    exists c, [/\ inc c y', inc u c & inc v c]).
  move=> u v ua va. 
  have p1: inc (J u v) (coarse a) by apply:setXp_i.
  have p2: (inc (J u v) (union (partition_relset_aux y' x))).
    rewrite eq; union_tac.
  have [z Jbb /Zo_P [zp [c cy zc]]] := (setU_hi p2).
  by exists c; split=> //; move: Jbb; rewrite zc; move/setXp_P => [].
have [c [cy bc _]] := (p _ _ ba ba).
suff: a = c by move=> ->.
set_extens t => ta.
  have [c' [cy' tc' _]] := (p _ _ ta ta).
  have [c'' [cy'' bc'' tc'']] :=  (p _ _ ba ta).
  case:((proj2 (proj1 pa') )_ _ cy cy'').
    move => ->; case:((proj2 (proj1 pa')) _ _ cy'' cy'); first by move => ->.
    by move=> dcf;case: (nondisjoint tc'' tc' dcf).
  by move=> dcf;case: (nondisjoint bc bc'' dcf).
have p1: (inc (J b t) (coarse c)) by apply:setXp_i.
have p2: (inc (J b t) (union (partition_relset_aux y' x))).
  apply: (setU_i p1); apply: (partition_relset_pr1 pa' cy).
move: p2; rewrite eq /partition_relset_aux => p2. 
have [z Jbb /Zo_P [zp [d dy zx]]]:= (setU_hi p2).
move: Jbb; rewrite zx; move/setXp_P => [bd td].
case:((proj2 (proj1 pa)) _ _ ay dy); first by move=> ->. 
move=> dfc; case: (nondisjoint ba bd dfc).
Qed.

(** Characterisation of graphs of orders and preorders. *)

Lemma preorder_prop1 g:
  sgraph g ->
  sub (diagonal (substrate g)) g -> sub (g \cg g) g ->
  g \cg g = g.
Proof. 
move=> gg sig scg; apply: extensionality; first by aw.
move => x xg; apply /compg_P; split; first by apply: gg.
exists (Q x); rewrite ? (gg _ xg) //;apply: sig; apply/diagonal_pi_P.
split => //;substr_tac.
Qed.

Lemma preorderP g: sgraph g ->
  (preorder g <-> (sub (diagonal (substrate g)) g /\ sub (g \cg g) g)).
Proof. 
move=> gg;split.
  move=> [_ rr tr]; split; move=> x.
    by move/diagonal_i_P=> [px Px pq]; rewrite -px -pq; apply: rr.
  move: tr;rewrite idempotent_graph_transitive //; apply.
move=> [s1 s2];split=> //.
  by move=> y ys; apply: s1; apply/diagonal_pi_P.
by rewrite idempotent_graph_transitive. 
Qed.


Theorem orderP r:
  order r <->
    (r \cg r = r /\ r \cap (opp_order r) = diagonal (substrate r)).
Proof.
split.
  move=> or.
  set (d:= diagonal (substrate r)).
  have i2: (r \cap (opp_order r) = d). 
    set_extens t.
      move /setI2_P => [tr /igraphP [pt Jr]].
      apply /diagonal_i_P;split => //; first by substr_tac.      
      rewrite -pt in tr; apply: (order_antisymmetry or tr Jr).
    move/diagonal_i_P => [pt Ps pq]. 
    rewrite -pt -pq.
    have rpp: (related r (P t) (P t)) by order_tac.
    by apply: setI2_i=>//; apply/igraph_pP. 
  have gr: (sgraph r) by fprops.
  have sd: (sub d r) by rewrite -i2; apply : setI2_1.
  have sc: (sub (d \cg r) (r \cg r))  by apply: compg_S; fprops.
  have crrr: (sub (r \cg r) r). 
     move: or => [_ _ t _];rewrite -idempotent_graph_transitive //. 
  by split =>//; apply: preorder_prop1. 
move=> [crrr iro].
have sr: sgraph r by rewrite -crrr;  apply: compg_graph.
split=> //.
- move=> y ys.
  have: (inc (J y y) (diagonal (substrate r))) by apply /diagonal_pi_P.
    by rewrite -iro; move=> Ji; apply: (setI2_1 Ji).
- have: sub (r \cg r) r by rewrite crrr; fprops.
  rewrite  -idempotent_graph_transitive //. 
- move => x y rxy ryx.
  have p1: (inc (J x y) (opp_order r)) by apply/igraph_pP.
  have: (inc (J x y) (diagonal (substrate r))). 
    by rewrite - iro; apply: setI2_i.
  by move /diagonal_pi_P => [_].
Qed.


Lemma order_structure s a:
  inc s (\Po (coarse a)) ->
  s \cg s = s ->
  s \cap (inverse_graph s) = diagonal a ->
  a = substrate s.
Proof.
move => /setP_P pa pb pc; set_extens t => ta.
  have : inc (J t t) (diagonal a) by apply /diagonal_pi_P.
  rewrite -pc => /setI2_P [ts _]; substr_tac.
have sg: sgraph s by rewrite - pb; fprops.
by case /(substrate_P sg): ta => [] [y ps]; move: (pa _ ps) => /setXp_P [pd pe].
Qed.

(** ** Preorder relations *)

Lemma preorder_reflexivity r a:
  preorder r -> (inc a (substrate r) <-> gle r a a).
Proof. 
move=> [g pr _]; split; first by apply: pr.  
rewrite/gle;move=> h; substr_tac.
Qed.
  
Lemma opposite_is_preorder1 r:
  preorder r -> preorder (opp_order r).
Proof. 
move=> [gr rr tr].
have go: (sgraph (opp_order r)) by fprops.
have ss: (sub (substrate (opp_order r)) (substrate r)).
  move=> t /(substrate_P go) [] [y] /igraph_pP => h; substr_tac.
split => //.
   by move=> y ys; apply /igraph_pP;apply: rr; apply: ss.
move => x y z /igraph_pP p1 /igraph_pP p2; apply /igraph_pP; apply: tr p2 p1.
Qed.

(** [r x y /\ r y x] is an equivalence relation, compatible with [r] *)

Definition symmetrize (r: relation) := fun x y => r x y  /\ r y x.

Lemma equivalence_preorder r:
  preorder_r r -> equivalence_r (symmetrize r).
Proof.
move=> [ tr _]; split; first by move=> x y [rxy ryx]. 
move=> x y z [xy yx] [yz zy]; split; [ apply: tr xy yz | apply: tr zy yx].
Qed.

Lemma compatible_equivalence_preorder r  (s := symmetrize r):
  preorder_r r -> forall x y x' y', r x y -> s x x' -> s y y' -> r x' y'. 
Proof. 
move=> [tr _] x y x' y' rxy [rxx' rx'x] [ryy' ry'y].
move: (tr _ _ _ rx'x rxy) => rx'y.
apply: tr rx'y ryy'.
Qed.

(** This is the graph of the equivalence associated *)

Definition equivalence_associated_o r:= r \cap (opp_order r).

Lemma eao_P r x y:  
   related (equivalence_associated_o r) x y <-> symmetrize (gle r) x y.
Proof.
split; first by move /setI2_P =>[pa] /igraph_pP pb; split.
by move => [pa pb]; apply:setI2_i => //; apply /igraph_pP.
Qed.

Lemma equivalence_preorder1 r:
  preorder r -> 
  equivalence (equivalence_associated_o r).
Proof.
move=> [gr _ tr].
have gi: sgraph (opp_order r) by fprops.
have gi2:= (setI2_graph2 gr (x:=r)).
have gi3: sgraph (r \cap (opp_order r)).
  by move=> x xi; apply: gr (setI2_1 xi).
apply: symmetric_transitive_equivalence => //.
  by move=> x y /eao_P [pa pb]; apply/eao_P.
move=> x y z /eao_P [xy yx] /eao_P [yz zy]; apply/eao_P.
split; [ apply: tr  xy yz | apply: tr  zy yx ].
Qed.

Lemma equivalence_associated_o_sr r:
  preorder r -> 
  substrate (equivalence_associated_o r) = substrate r.
Proof. 
move=> pr.
have eq:=  (equivalence_preorder1 pr).
set_extens x => xs. 
  move: (reflexivity_e eq xs) => /eao_P [pa _]; order_tac.
move: pr=> [gr rr _].
by apply: (arg1_sr (y:=x)); move : (rr _ xs) => t;apply/eao_P.
Qed.

Lemma compatible_equivalence_preorder1 r u v x y:
  preorder r -> related r x y -> 
  related (equivalence_associated_o r) x u -> 
  related (equivalence_associated_o r) y v ->
  related r u v.
Proof. 
move => pr rxy /eao_P [_ pb] /eao_P [pc _].
move: pr => [_ _ tr]; apply: tr (tr _ _ _ pb rxy) pc.
Qed.


(** If [r] is a preorder, [e] the associated equivalence, [E] the quotient,
  the relation induced by [r] on [E] is an ordering *)

Definition order_associated r :=
  let s := graph (canon_proj (equivalence_associated_o r)) in 
  (s \cg r) \cg (opp_order s).

Lemma oap_graph r: sgraph (order_associated r).
Proof. apply: compg_graph. Qed.

Lemma compose3_relP s r u v:
  related ((s \cg r) \cg (opp_order s)) u v <->
  exists x y, [/\ related s x u, related s y v& related r x y].
Proof. 
split. 
  by move/compg_pP => [z /igraph_pP pa /compg_pP [y pb pc]]; exists z, y.
move=> [x [y [xu yv xy]]]; apply/compg_pP;exists x; first by apply/igraph_pP.
by apply/compg_pP; exists y.
Qed. 

Section OrderAssociated.
Variable (r:Set).
Hypothesis pr: preorder r. 

Lemma oap_relP1 u v:
  related (order_associated r) u v <->
  [/\ inc u (quotient (equivalence_associated_o r)) ,
    inc v (quotient (equivalence_associated_o r)) &
    exists x y, [/\ inc x u, inc y v & related r x y]].
Proof. 
set s:= equivalence_associated_o r.
set p:= graph (canon_proj s).
rewrite /order_associated -/s -/p.
have es:equivalence s by apply: equivalence_preorder1.
split.
  move /compose3_relP=> [x [y [xu yv xy]]].
  have fc: function (canon_proj s) by apply: canon_proj_f.
  move: (p1graph_source fc xu); aw => xs.
  move: (p1graph_source fc yv); aw => ys.
  have: (u = Vf (canon_proj s) x) by apply: Vf_pr. 
  have: (v = Vf (canon_proj s) y) by apply: Vf_pr.
  rewrite canon_proj_V // canon_proj_V //.
  move=> -> ->; split; fprops.
  exists x, y; split => //; first by apply: inc_itself_class. 
  by apply: inc_itself_class.  
move=> [uq vq [x [y [xu yv xy]]]]; apply /compose3_relP.
exists x, y; split => //.
apply/(rel_gcp_P es) => //; apply: (inc_in_setQ_sr es xu uq). 
apply/(rel_gcp_P es) => //; apply: (inc_in_setQ_sr es yv vq). 
Qed.

Lemma oap_relP2 u v:
  related (order_associated r) u v <->
  [/\ inc u (quotient (equivalence_associated_o r)),
    inc v (quotient (equivalence_associated_o r)) &
    forall x y, inc x u -> inc y v -> related r x y].
Proof.
set (s:= equivalence_associated_o r). 
have es: equivalence s by rewrite /s; apply: equivalence_preorder1.
split.
  move /oap_relP1 => [uq vq [x [y [xu yv xy]]]]; split=> //.
  move=> a b au bv.
  have xa: (related s x a).
    by apply /(in_class_relatedP es); exists u; split => //;apply/(setQ_P es).
  have yb: (related s y b).
    by apply /(in_class_relatedP es); exists v;split => //; apply/(setQ_P es).
  apply: (compatible_equivalence_preorder1 pr xy xa yb).
move => [uq vq hyp]; apply/oap_relP1;split => //.
move: (setQ_repi es uq)  (setQ_repi es vq) => pa pb.
by exists (rep u); exists (rep v);split => //; apply: hyp.
Qed.

Lemma oap_osr:
  order_on (order_associated r)(quotient (equivalence_associated_o r)).
Proof.
have ea:equivalence (equivalence_associated_o r).
  by apply: equivalence_preorder1.
set eao:= (equivalence_associated_o r).
have prop: forall a b, inc (J a b) (order_associated r)-> 
  (inc a (quotient eao) /\ inc b (quotient eao)).
  move=> a b Jab.
  have: (related (order_associated r) a b) by done.
  by move/oap_relP2=> [pa pb _].
have sr:substrate (order_associated r) = quotient eao.
  set_extens x. 
    move:(@oap_graph r) => h.
    by move/(substrate_P h) => [][y /oap_relP2 [pa pb _]].
  move=> xq; apply: (arg1_sr (y:=x));apply/oap_relP2; split => // z y zx yx.
  suff: symmetrize (gle r) z y by move => [].
  apply/eao_P; apply/(in_class_relatedP ea).
  by exists x;split => //; apply/(setQ_P ea).
have go: sgraph (order_associated r) by apply: oap_graph.
split => //.
move:(pr)=> [rr gr tr]; split => //.
   hnf; rewrite sr => y ys;apply/oap_relP2; split => // x z xy zy.
   have: (related  (equivalence_associated_o r) x z). 
     by apply/(in_class_relatedP ea); exists y; split=>//; apply/(setQ_P ea).
    by move/eao_P=> [].
  move=> x y z /oap_relP2 [xq yq rxy]/oap_relP2 [_ zq ryz].
  apply/oap_relP2;split => // a b ax bz; move: (setQ_repi ea yq) => cy.
  apply: tr (rxy _ _ ax cy) (ryz _ _  cy bz).
move=> x y /oap_relP2 [xq yq rxy] /oap_relP2 [_ _ ryx].
move:(setQ_repi ea xq) (setQ_repi ea yq) => ax biy.
move: (rxy _ _ ax biy)(ryx _ _ biy ax)=> rab rba.
move: (conj rab rba); move /eao_P=> reab.
move: xq yq => /(setQ_P ea) cx  /(setQ_P ea) cy.
have bx: inc (rep y) x by apply: (rel_in_class2 ea cx reab).
case: (class_dichot ea cx cy) =>// hyp.
case: (nondisjoint bx biy hyp).
Qed.

Lemma oap_pr:
  order_associated r =
    Vfs ( canon_proj (equivalence_associated_o r) \ftimes
    (canon_proj (equivalence_associated_o r))) r.
Proof.
set (s:= equivalence_associated_o r).
have es:equivalence s by rewrite /s; apply: equivalence_preorder1.
have ss:substrate s = substrate r. 
  by rewrite /s equivalence_associated_o_sr.    
have fep: function (ext_to_prod (canon_proj s) (canon_proj s)).
  by apply: ext_to_prod_f; apply: canon_proj_f.
have gi: sgraph (Vfs (ext_to_prod (canon_proj s) (canon_proj s)) r).
  move=> t /dirim_P [x xr Jg].
  by move:(p2graph_target fep Jg); rewrite lf_target; move/setX_P => [].
apply/sgraph_exten=> //; first by apply: oap_graph. 
move=> u v; split.
  move/oap_relP2=> [uq vq hyp]; apply/dirim_P;exists (J (rep u) (rep v)).  
    by apply: hyp; apply: (setQ_repi es).  
  have: (J u v = J (class s (rep u)) (class s (rep v))) by rewrite ! class_rep.
  rewrite - ext_to_prod_rel_V; fprops; move =>->.
  by apply: Vf_pr3=> //; rewrite /ext_to_prod; aw; fprops.
move/dirim_P=> [x xr Jg]; move: (Vf_pr fep Jg)=> Wx. 
have px: (pairp x) by move: pr=> [g _ _]; apply: g.
have ps: (inc (P x) (substrate s)) by rewrite ss; substr_tac.
have qs: (inc (Q x) (substrate s)) by rewrite ss; substr_tac.
move: Wx; rewrite -px ext_to_prod_rel_V // => JJ.
rewrite (pr1_def JJ) (pr2_def JJ). 
apply/oap_relP2;split;fprops => a b au bv.
suff: (related (order_associated r) (class s (P x)) (class s (Q x))). 
  by move /oap_relP2 => [_ _ h]; apply: h au bv.
apply /oap_relP1;split; fprops.
exists (P x), (Q x); split ; try apply: (inc_itself_class es) => //.
by hnf; rewrite px.
Qed.


End OrderAssociated.

(** ** Notation and terminology *)


(** Bourbaki defines an ordering [r] of [s] to be a set satisfying the following condition *)

Definition order_axioms r s :=
  [/\ (forall y x z, gle r x y ->  gle r y z -> gle r x z),
      (forall x y, gle r x y ->  gle r y x -> x = y),
      (forall x y, gle r x y ->  (inc x s /\ inc y s)),
      (forall x, gle r x x <-> inc x s) &
       sgraph r].

Lemma axioms_of_order r:
  order r <-> (order_axioms r (substrate r)).
Proof. 
rewrite/order_axioms; split.
move => [p1 p2 p3 p4].
  split => //.
    by move => x y xy; split; order_tac.
  by move => x; split => h; try order_tac; apply: p2.
move=> [h1 h2 h3 h4 gr]; split => //; by move => y /h4.
Qed.

(** A morphism is a function that preserves ordering. It is injective.
When bijective it is called an isomorphism. We show stability by composition *)

Definition fincr_prop f r r' := 
  forall x y,  gle r x y  -> gle r' (Vf f x) (Vf f y).
Definition fsincr_prop f r r' := 
  forall x y,  glt r x y  -> glt r' (Vf f x) (Vf f y).

Definition fiso_prop f r r' := 
  forall x y, inc x (source f) -> inc y (source f) ->
    (gle r x y <-> gle r' (Vf f x) (Vf f y)).
Definition fsiso_prop f r r' := 
  forall x y, inc x (source f) -> inc y (source f) ->
    (glt r x y <-> glt r' (Vf f x) (Vf f y)).

Definition order_isomorphism f r r' :=
  [/\ order r, order r', bijection_prop f (substrate r) (substrate r')&
  fiso_prop f r r'].

Definition order_morphism f r r' :=
  [/\ order r, order r', function_prop f (substrate r) (substrate r') &
  fiso_prop f r r'].

Definition order_isomorphic r r':=
  exists f, order_isomorphism f r r'.
Notation "x \Is y" := (order_isomorphic x y) (at level 50).

Lemma order_morphism_fi f r r':  order_morphism f r r'->
  injection f.
Proof.
move => [or or' [ff sf tf] h].
split => // x y xsf ysf sv.
have aux: gle r' (Vf f y) (Vf f y) by order_tac; Wtac.
apply: (order_antisymmetry or).  
  apply/(h _ _  xsf ysf); ue. 
apply/(h _ _  ysf xsf); ue.
Qed.

Lemma order_isomorphism_w r r' f:
  order_isomorphism f r r' -> order_morphism f r r'.
Proof. by move=> [or or' [ [[ff _] _] sf tf] etc]. Qed.


Lemma order_isomorphism_ws r r' f:
  bijection f -> order_morphism f r r' -> order_isomorphism f r r'.
Proof. by move=> bf [or or'[ _ sf tf] etc]. Qed.

Lemma order_morphism_incr f r r': order_morphism f r r' -> fincr_prop f r r'.
Proof. 
move =>  [or or' [ff sf tf] h] x y rxy.
have xsr: inc x (source f) by rewrite sf; order_tac.
have ysr: inc y (source f) by rewrite sf; order_tac.
by move/(h _ _  xsr ysr):rxy.
Qed.

Lemma order_isomorphism_incr f r r':
  order_isomorphism f r r' -> fincr_prop f r r'.
Proof. 
by move => h; apply: order_morphism_incr; apply:order_isomorphism_w.
Qed.

Lemma order_morphism_sincr f r r': order_morphism f r r' -> fsincr_prop f r r'.
Proof. 
move => h; move: (order_morphism_fi h) => fi.
move: h => [or or' [ff sf tf] h] x y [rxy nxy].
have xsr: inc x (source f) by rewrite sf; order_tac.
have ysr: inc y (source f) by rewrite sf; order_tac.
split; first by move/(h _ _  xsr ysr):rxy.
by dneg aux; apply: (proj2 fi).
Qed.

Lemma order_isomorphism_sincr f r r':
  order_isomorphism f r r' -> fsincr_prop f r r'.
Proof. 
by move => h; apply: order_morphism_sincr; apply:order_isomorphism_w.
Qed.

Lemma order_morphism_siso f r r': order_morphism f r r' -> fsiso_prop f r r'.
Proof. 
move => h x y xsf ysf; split; first by apply :order_morphism_sincr.
have fi :=(order_morphism_fi h).
have [or or' [ff sf tf] hp] := h.
by move => [pa pb]; split; [ apply /hp | move => h1; case: pb; rewrite h1].
Qed.

Lemma order_isomorphism_siso f r r': order_isomorphism f r r' ->
   fsiso_prop f r r'.
Proof. 
by move => h; apply: order_morphism_siso; apply:order_isomorphism_w.
Qed.

Lemma identity_is r: order r ->
  order_isomorphism (identity (substrate r)) r r.
Proof.  
move=> or; hnf; rewrite  /fiso_prop; aw; trivial;split => //.
  saw;apply: identity_fb.
move=> x t xsr ysr; rewrite ? idV //.  
Qed.

Lemma identity_morphism r: order r ->
  order_morphism (identity (substrate r)) r r.
Proof. 
by move=> or; apply: order_isomorphism_w; apply: identity_is.
Qed.

Lemma compose_order_morphism  r r' r'' f f':
  order_morphism f r r' -> order_morphism f' r' r'' ->
  order_morphism (f' \co f) r r''.
Proof.
move=>[or or' [ff sf tf] fp][_ or'' [ff' sf' tf'] fp'].
have cff': f' \coP f by split => //; rewrite sf'.
split => //; first by saw;fct_tac.
hnf; aw; move=> x y xsf ysf; rewrite !compfV //.
move: (Vf_target ff xsf)(Vf_target ff ysf); rewrite tf - sf' => xt yt.
split; first by  move => h; apply /(fp' _ _  xt yt) /(fp _ _  xsf ysf).
by move/(fp' _ _  xt yt)  /(fp _ _  xsf ysf).
Qed.

Lemma compose_order_is r r' r'' f f':
  order_isomorphism f r r' -> order_isomorphism f' r' r'' ->
  order_isomorphism (f' \co f) r r''.
Proof.
move => pa pb;
move: (order_isomorphism_w pa) (order_isomorphism_w pb) => h1 h2.
apply: order_isomorphism_ws (compose_order_morphism h1 h2).
move: pa pb =>[_ _ [bf sf tf] _][_ _ [bf' sf' tf'] _].
by apply: compose_fb => //; split => // ; try fct_tac; rewrite  sf'.
Qed.

Lemma inverse_order_is r r' f:
   order_isomorphism f r r' -> order_isomorphism (inverse_fun f) r' r.
Proof. 
rewrite /order_isomorphism. 
move=>[or or' [bf sf tf] fp];saw. 
  by split; aw => //; apply: inverse_bij_fb. 
move=> x y xt yt.
move: (xt)(yt); aw => xt1 yt1.
rewrite -{1}  (inverse_V bf xt1) -{1} (inverse_V bf yt1).
have aux: (source f = target (inverse_fun f)) by aw.
move: (inverse_bij_fb bf) => [[fi _] _].
symmetry;apply/fp; rewrite aux; Wtac.
Qed.

Lemma orderIR r: order r ->  r \Is r.
Proof. by move=> or; exists (identity (substrate r)); apply: identity_is. Qed.

Lemma orderIS r r': r \Is r' -> r' \Is r. 
Proof.
move=> [f fi]; exists (inverse_fun f); apply: (inverse_order_is fi).
Qed.

Lemma orderIT r' r r'':  r \Is r' -> r' \Is r'' -> r \Is r''.
Proof. 
move=> [f oif][g oig]; exists (g \co f); apply: (compose_order_is oif oig).
Qed. 


(** ** Ordered subsets. Product of ordered sets *)

(** Order induced by [r] on [a] *)

Definition induced_order r a := r \cap (coarse a).

Lemma iorder_gleP r a x y:
  gle (induced_order r a) x y <-> [/\ inc x a, inc y a & gle r x y].
Proof.
split; first by move/setI2_P => [h /setXp_P [pa pb]].
by move => [pa pb pc]; apply /setI2_i => //;apply/setXp_P.
Qed.

Lemma iorder_gltP r a x y:
  glt (induced_order r a) x y <-> [/\ inc x a, inc y a & glt r x y].
Proof. 
split; first by move => [] /iorder_gleP [pa pb pc] pd.
by move => [pa pb [pc pd]]; split => //; apply /iorder_gleP.
Qed.

Lemma iorder_gle0P r a x y: inc x a -> inc y a -> 
  (gle (induced_order r a) x y <-> gle r x y). 
Proof. 
move=> xa ya;split;first by case/iorder_gleP. 
by move => pa;  apply /iorder_gleP.
Qed.

Lemma iorder_gle1 r a x y:
  gle (induced_order r a) x y -> gle r x y. 
Proof. by move/iorder_gleP=> [_ _].  Qed.

Lemma iorder_gle2 r a x y:
  glt (induced_order r a) x y -> glt r x y. 
Proof. by move/iorder_gltP=> [_ _]. Qed.

Lemma iorder_gle3 r a x y:
  gle (induced_order r a) x y -> (inc x a /\ inc y a).
Proof. by move/iorder_gleP=> [pa pb _]. Qed.

Lemma iorder_gle4 r a x y:
  glt (induced_order r a) x y -> (inc x a /\ inc y a).
Proof. by move/iorder_gltP=> [pa pb _]. Qed.


Lemma iorder_equivalence r x: sub x (substrate r) -> equivalence r ->
  equivalence (induced_order r x).
Proof.
move => sxr [qa qb qc qd].
split => //.
- by move => a /setI2_P/proj2/setX_P/proj31.
- move => a asr.
  suff ax: inc a x by  apply/iorder_gleP; split => //; apply: qb; apply: sxr.
  by case /setU2_P: asr => /funI_P [z /setI2_P [zr /setX_P [za zb zc]] ->].
- move => b a c /iorder_gleP [ax bx ha]  /iorder_gleP[_ cx hb].
  apply/ iorder_gleP; split => //; apply: qc ha hb.
- move => a b /iorder_gleP [ax bx ha]; apply /iorder_gleP; split => //.
  by apply: qd. 
Qed.
Lemma iorder_preorder r a:
  sub a (substrate r) -> 
  preorder r -> preorder (induced_order r a).
Proof. 
move=> ar [gr rr tr].
have gi: sgraph (induced_order r a) by apply: (setI2_graph1 gr (y:=coarse a)).
hnf; split => //.
  move => t ti.
  have ta: inc t a. 
    by move: ti => /(substrate_P gi) [] [y]/iorder_gleP [ta tb _].
  by apply /iorder_gleP;split => //;apply: rr; apply: ar.
move=> x y z /iorder_gleP [xa ya rxy] /iorder_gleP [_ za ryz].
apply/iorder_gleP;split => //; apply: tr rxy ryz.
Qed.

Lemma iorder_osr r a: order r -> sub a (substrate r) ->
  order_on (induced_order r a) a.
Proof. 
move=> ar or.
have: preorder (induced_order r a).
  by apply: iorder_preorder =>//; apply: order_preorder.
move=> [go rio tio]; split.
  split => // x y /iorder_gleP [_ _ rxy] /iorder_gleP [_ _ ryz]; order_tac.
set_extens t.
   by move/(substrate_P go) => [] [y] /iorder_gleP [pa pb _].
move => ta; move: (or _ ta) => tb. 
by apply /(substrate_P go); left; exists t; apply /iorder_gle0P => //;order_tac.
Qed.

Lemma iorder_sr r a: order r -> sub a (substrate r) ->
  substrate (induced_order r a) = a.
Proof. move => pa pb; exact: (proj2 (iorder_osr pa pb)). Qed.

Hint Rewrite iorder_sr : bw.

Lemma induced_order_empty r: induced_order r emptyset = emptyset.
Proof. by apply/set0_P => t /setI2_P [_] /setX_P [_ /in_set0]. Qed.


Lemma iorder_substrate r:
  order r -> induced_order r (substrate r) = r.
Proof.
move=> o;apply/setI2id_Pl;apply: sub_graph_coarse_substrate; fprops.
Qed.

Lemma ipreorder_sr r a: preorder r -> sub a (substrate r) ->
  substrate (induced_order r a) = a.
Proof.
move => ha hb.
have /substrate_P sp: sgraph (induced_order r a).
  by move => t /setI2_P [_]/setX_P[].
set_extens t.
   by move/sp => [] [y] /iorder_gleP [pa pb _].
move => ta; move: (hb _ ta) => tb. 
apply /sp; left; exists t; apply /iorder_gle0P => //.
by apply: (proj32 ha).
Qed.

Lemma iorder_trans a b c: sub c b -> 
  induced_order (induced_order a b) c = induced_order a c.
Proof.
move=> cb; rewrite /induced_order.  
have scc: (sub (coarse c) (coarse b)) by apply:setX_Sll.
by rewrite - setI2_A; congr intersection2; apply/setI2id_Pr.
Qed.

Lemma iorder_opposite r x: order r ->
  commutes_at (induced_order ^~ x) (opp_order) r.
Proof. 
move => or.
apply: sgraph_exten.
    apply: (setI2_graph2); apply: coarse_graph.
  apply: igraph_graph.
move => u v; split.
   move /iorder_gleP => [pa pb /igraph_pP pc]. 
   by apply/igraph_pP; apply /iorder_gleP.
 move/igraph_pP => /iorder_gleP [pa pb pc].
by apply /iorder_gleP;split => //; apply /igraph_pP.
Qed.

(** Example 1. The function that associates to a partial function its graph. 
   Is an isomorphism for extends and inclusion *)


Definition graph_of_function x y :=
  Lf graph (sub_functions x y)  (fgraphs x y).


Lemma set_of_graphs_pr x y z:
  inc z (sub_functions x y) -> inc (graph z) (fgraphs x y).
Proof. 
move => /sfunctionsP [ff  sf <-]; apply/fgraphsP. 
by move: (f_range_graph ff) => rr; case ff => _ qa <-.
Qed.

Lemma graph_of_function_f x y:
  function (graph_of_function x y).
Proof. by apply: lf_function; apply: set_of_graphs_pr. Qed.

Lemma graph_of_function_V x y f:
  inc f (sub_functions x y) -> Vf (graph_of_function x y) f = graph f.
Proof. 
rewrite /graph_of_function=> fs; rewrite LfV //; apply: set_of_graphs_pr.
Qed.

Lemma graph_of_function_fb x y:
  bijection (graph_of_function x y).
Proof. 
rewrite /graph_of_function.
apply: lf_bijective.
    by apply: set_of_graphs_pr.
  move=> u v /sfunctionsP [fu ssu tu] /sfunctionsP [fv sv tv] sg.
  by apply: function_exten1=>//; ue.
move=> z /Zo_P [] /setP_P zp fx.
have gz:= (sub_setX_graph zp).
exists (triple (domain z) y z); last by  aw.
apply/sfunctionsP;saw.
  apply: function_pr => //.
  by move => t /(rangeP gz) [u Jz]; move: (zp _ Jz) => /setXp_P [].
by move => t /(domainP gz) [u Jz]; move: (zp _ Jz) => /setXp_P [].
Qed.



Lemma graph_of_function_is x y:
  order_isomorphism (graph_of_function x y)
  (opp_order (extension_order x y))
  (sub_order (fgraphs x y)).
Proof. 
have [eo sr]:= (extension_osr x y).
have [sio sis] := (sub_osr (fgraphs x y)).
have [ex sx]:= (opp_osr eo).
hnf; rewrite /fiso_prop sis sx sr.
have <- :sub_functions x y = source (graph_of_function x y).
  by rewrite /graph_of_function; aw.
split; fprops.
   rewrite /graph_of_function; saw.
   by apply: graph_of_function_fb. 
move=> a b ass bss.
rewrite graph_of_function_V // graph_of_function_V //. 
split. 
   move /extension_order_P2 => [_ _ h]; apply/sub_gleP. 
   by split => //; apply: set_of_graphs_pr.
by move /sub_gleP => [pa pb pc]; apply /extension_order_P2.
Qed.

(** Example 2. The mapping that associates to a partition the graph of 
the equivalence is an order isomorphism onto its image*)

Definition graph_of_partition x := 
  Lf (fun y => partition_relset y x) (partitions x) (\Po (coarse x)).

Lemma gop_axioms x:
  lf_axiom (fun y => partition_relset y x)
     (partitions x) (\Po (coarse x)).
Proof. 
by move=> y /partitionsP => h; apply/setP_P /sub_part_relsetX.
Qed.

Lemma gop_V x y: 
  partition_s y x ->
  Vf (graph_of_partition x) y = partition_relset y x.
Proof. 
rewrite /graph_of_partition=> pa; rewrite LfV //; first by apply: gop_axioms. 
by apply /partitionsP.
Qed.

Lemma gop_morphism x:
  order_morphism (graph_of_partition x) (coarser x)
  (opp_order (subp_order (coarse x))).
Proof.
have [oi sr] := (sub_osr (coarse x)).
have [oc sr'] := (coarser_osr x).
have [pa1 pb1] := (subp_osr (coarse x)).
have [pa2 pb2] := (opp_osr pa1).
have gi: (sgraph (sub_order (coarse x))) by fprops.
have sg: source (graph_of_partition x) = (partitions x).
  by rewrite /graph_of_partition; aw.
split;fprops.
  split; rewrite ? pb2 ? pb1 ? sr' /graph_of_partition;aw; trivial.
  by apply: lf_function; apply: gop_axioms.
hnf;rewrite sg => a b /partitionsP pa /partitionsP pb.
rewrite - partition_relset_order // gop_V // gop_V //. 
split; last by move/igraph_pP => /sub_gleP [_ _].
move => h; apply/igraph_pP; apply /sub_gleP. 
by split => //; apply /setP_P /sub_part_relsetX.
Qed.

(** Example 3: Compare preorder relations *)

Definition preorder_on r E := preorder r /\ substrate r = E.
Definition preorders x :=
  Zo (\Po (coarse x))(preorder_on ^~ x).

Lemma preordersP x z:
  inc z (preorders x) <-> (preorder_on z x).
Proof. 
split; first by move/Zo_P => [].
move => h;apply:Zo_i => //;apply/setP_P.
by move: h => [pa <-]; apply:sub_graph_coarse_substrate; apply: preorder_sgraph.
Qed.

Definition coarser_preorder x := sub_order (preorders x).

Lemma coarser_preorder_osr x:  
  order_on (coarser_preorder x) (preorders x).
Proof. exact: sub_osr. Qed.

Lemma coarser_preorder_gleP x u v:
  gle (coarser_preorder x) u v <->
  [/\ preorder u, preorder v, substrate u = x, substrate v = x & sub u v].
Proof. 
split; first by move/sub_gleP => [] /Zo_hi [xa pa] /Zo_hi [ya pb] pc.
move => [pa pb pc pd pe]; apply /sub_gleP.
by split => //; apply /preordersP.
Qed.

Lemma coarser_preorder_gleP1 x u v:
  gle (coarser_preorder x) u v <->
  [/\ preorder u, preorder v, substrate u = x, substrate v = x &
  forall a b, inc a x -> inc b x -> related u a b -> related v a b].
Proof. 
split.
  move/coarser_preorder_gleP => [pu pv su sv hyp]; split => //.
  by move=> a b ax bx J1; apply: hyp.
move => [pu pv su sv hyp].
apply /coarser_preorder_gleP; split => // t tu.
have p:= (preorder_sgraph pu tu).
rewrite -p in tu |- *; apply: hyp =>//; rewrite - su; substr_tac.
Qed.


(** If [g] is a family of orders, we consider [f] the family of susbtrates.
We consider here the ordering induced by [g] on the product of [f] *)

Definition fam_of_substrates g := 
  Lg (domain g) (fun i => substrate (Vg g i)).

Definition prod_of_substrates g := productb (fam_of_substrates g).

Definition order_fam g := allf g order.

Definition order_product_r g x x' :=
   forall i, inc i (domain g) -> gle (Vg g i) (Vg x i) (Vg x' i).

Definition order_product g := 
  graph_on (order_product_r g)(prod_of_substrates g).

Lemma fos_graph f: fgraph (fam_of_substrates f).
Proof. rewrite /fam_of_substrates; fprops. Qed.

Lemma fos_d f: domain (fam_of_substrates f) = domain f.
Proof. by rewrite /fam_of_substrates; aw. Qed.

Lemma fos_V f x: inc x (domain f) ->
   Vg (fam_of_substrates f) x = substrate (Vg f x).
Proof. by move => xdf; rewrite LgV. Qed.


Hint Rewrite fos_d : aw.

Lemma prod_of_substratesP g x:
  inc x  (prod_of_substrates g) <-> 
   [/\ fgraph x, domain x = domain g &
    forall i, inc i (domain g) -> inc (Vg x i) (substrate (Vg g i))].
Proof. 
split.
  move/setXb_P; aw; move=> [fgx dx asu];split => //.
  by move => i idg; move: (asu _ idg); rewrite LgV.
move => [pa pb pc]; apply /setXb_P; aw;split=> // i idg.
rewrite LgV //; exact: (pc _ idg).
Qed.

Lemma prod_of_substrates_p g x i:
  inc x (prod_of_substrates g) ->
  inc i (domain g) -> inc (Vg x i) (substrate (Vg g i)).
Proof. case/(prod_of_substratesP) => _ _; apply. Qed.

Lemma prod_of_substrates_gi g f:
  (forall i, inc i (domain g) -> inc (f i) (substrate (Vg g i))) ->
  inc (Lg (domain g) f) (prod_of_substrates g).
Proof.
move => pb; apply/(prod_of_substratesP);split => //; aww=> i idg.
by rewrite LgV //; apply: pb.
Qed.

Lemma order_product_gleP g x x':
  (gle (order_product g) x x' <-> 
    [/\ inc x (prod_of_substrates g),  inc x' (prod_of_substrates g) &
      forall i, inc i (domain g) -> gle (Vg g i) (Vg x i)(Vg x' i)]).
Proof. apply /graph_on_P0.  Qed.

Lemma order_product_osr g:
  order_fam g -> order_on (order_product g) (prod_of_substrates g).
Proof. 
move=> poa; move: (poa) => oa; split.
  rewrite /order_product/order_product_r. 
  apply: order_from_rel1.
  - move=> /= x y z pxy pyz i idg.
    move: (pxy _ idg) (pyz _ idg)(oa _ idg) => le1 le2 or; order_tac.
  - move=> x y; rewrite /prod_of_substrates => xp yp p1 p2. 
    apply: (setXb_exten xp yp); aw.
    move=> i idg; move: (p2 _ idg) (p1 _ idg)(oa _ idg) =>le1 le2 or; order_tac.
  - move=> u up i idg; move: (oa _ idg) => oi.
    by order_tac; apply: prod_of_substrates_p.
apply: graph_on_sr  => a ap i idg; move: (poa _ idg) => oi.
by order_tac; apply:prod_of_substrates_p.
Qed.


Definition fam_of_opp g := Lg (domain g) (fun i => opp_order (Vg g i)).

Lemma fam_of_opp_sr g: allf g sgraph -> 
   fam_of_substrates g =  fam_of_substrates (fam_of_opp g).
Proof.
rewrite /fam_of_opp /fam_of_substrates; aw => h.
apply: Lg_exten => i idg; aw;  move: (h i idg) => sg.
by rewrite LgV//  /substrate (igraph_range sg) (igraph_domain sg) setU2_C.
Qed.

Lemma fam_of_opp_or g: order_fam g -> order_fam (fam_of_opp g).
Proof. 
move => h i; rewrite /fam_of_opp Lgd => ig; rewrite LgV//.
exact: (proj1 (opp_osr (h i ig))).
Qed.

Lemma order_product_opp_osr g: order_fam g -> 
    order_on  (order_product (fam_of_opp g)) (prod_of_substrates g) /\
    order_product (fam_of_opp g) = opp_order (order_product g).
Proof.
move => ofg.
set g' := fam_of_opp g.
have ha: allf g sgraph by move => i /ofg [].
have hb: domain g = domain g' by rewrite /g' /fam_of_opp; aw.
move: (fam_of_opp_sr ha); rewrite  -/g' => ff'.
have ss': (prod_of_substrates g')= (prod_of_substrates g).
  by rewrite /prod_of_substrates ff'.
have hc: order_fam g' by apply:fam_of_opp_or.
move: (order_product_osr hc); rewrite ss' => hd; split => //.
move: (order_product_osr hc) => [opg' spg'].
move: (order_product_osr ofg) => [opg spg].
move: (opp_osr opg) => [ro _].
apply:order_exten => // x y; split. 
   move /order_product_gleP => [pa pb pc]; apply /opp_gleP.
   apply/order_product_gleP; split; rewrite -? ss' // => i idg.
   apply /opp_gleP.
   rewrite hb in idg; move:(pc _ idg); rewrite LgV//; ue.
move /opp_gleP /order_product_gleP => [pa pb pc].
apply/order_product_gleP; split; rewrite ? ss' // => i idg.
rewrite - hb in idg; move:(pc _ idg); rewrite LgV//  => hh.
by apply /opp_gleP.
Qed.

(** Let [g] be a family of orders, [f] the family of substrates, [p] the product 
of [f] and [r] the product order of the family [g]; its substrate is [p].
There a canonical bijection from [product p p] onto the product of all 
[product (f i) (f i)]. The bijection maps [r] to the product of [g]*)


Lemma product_order_def g (f := fam_of_substrates g):
  order_fam g -> 
  Vfs (prod_of_products_canon f f) (order_product g) = (productb g).
Proof.
set opg:= order_product g => oa.
have dfdg: domain f = domain g by rewrite /f; aw.
set (F:= triple (domain f) (range f) f).
have ff: fgraph f by apply: fos_graph.
have fF: function F by rewrite /F;  apply: function_pr;fprops.
have gF: graph F = f by rewrite /F; aw.
have fp: function (prod_of_products_canon f f).
  move: (popc_fb fF fF (refl_equal (source F))); rewrite gF=> h; fct_tac.
move:(order_product_osr oa) => [op poo].
have spgs: sub opg (source (prod_of_products_canon f f)).
  rewrite /prod_of_products_canon; aw.  
  have gpo: sgraph opg by fprops. 
  by move: (sub_graph_coarse_substrate gpo); rewrite poo.
set_extens x.
  move /(Vf_image_P fp spgs) => [u upo].
  move: (spgs _ upo); rewrite {1} /prod_of_products_canon lf_source -gF => upob.
  rewrite popc_V // => ->.
  move: upob; rewrite gF. 
  move /setX_P => [pu /setXb_P [fgP dPu alp] /setXb_P [fgQ dQu alq]].
  apply /setXb_P; rewrite /prod_of_fgraph;split; aww.
    by rewrite dPu dfdg.
  move=> i idg; rewrite LgV //;last by rewrite  dPu dfdg.
  have: (gle opg (P u) (Q u)) by hnf; rewrite pu.
  by move /(order_product_gleP) => [_ _ h]; move: (h _ idg) => wp; aw.    
set x1:= Lg (domain g) (fun i => P (Vg x i)).
set x2:= Lg (domain g) (fun i => Q (Vg x i)).
move/setXb_P => [fgx dxdg idx].
have p1: inc x1 (prod_of_substrates g).
  by apply: (prod_of_substrates_gi) => // i idg; apply: pr1_sr; apply: idx.
have p2: inc x2 (prod_of_substrates g). 
  by apply: (prod_of_substrates_gi) => // i idg; apply: pr2_sr;  apply: idx.
have p3 i: inc i (domain g) -> pairp (Vg x i).
   move=> idg; apply: (order_sgraph  (oa _ idg) (idx _ idg)).
apply/(Vf_image_P fp spgs); exists (J x1 x2).
  apply/(order_product_gleP);split => // i idg.
  by rewrite ! LgV// /gle /related (p3 _ idg); apply: idx. 
rewrite -gF popc_V //.
  symmetry.
  aw; rewrite /prod_of_fgraph /x1 /x2; apply:fgraph_exten=> //; aw; fprops.
  by move => i idg; rewrite ! LgV //; apply: p3.
by rewrite gF; apply: setXp_i.
Qed.

(** Special case of a product of 2 orders *)

Definition order_product2 f g := prod_of_relation f g.

Lemma order_product2_P f g x x':
  gle (order_product2 f g) x x' <->
  [/\ inc x ((substrate f) \times (substrate g)),
    inc x' ((substrate f)\times (substrate g)) &
    gle f (P x) (P x') /\ gle g (Q x) (Q x')].
Proof.
split; first by move/Zo_P =>[] /setXp_P; aw; move => [pa pb] pc.
by move => [pa pb pc]; apply: Zo_i; [apply:setXp_i | aw ].
Qed.


(** Order on graphs of functions [x->y], 
   induced by an order [g] on the target. 
   This is a special case of product order.
 *) 

Definition order_graph_r x r z z' := 
  forall i, inc i x -> gle r (Vg z i) (Vg z' i).

Definition order_graph x y r :=
  graph_on (order_graph_r x r) (gfunctions x y).

Lemma order_fam_cst x r: order r ->  order_fam (cst_graph x r).
Proof. by rewrite /cst_graph=> og; hnf; aw => i id; rewrite LgV. Qed.

Lemma order_graph_r_P x r z z':
  order_graph_r x r z z' <->
  order_product_r (cst_graph x r) z z'.
Proof.
have dc: (domain (cst_graph x r) = x) by aw.
rewrite /order_product_r dc /cst_graph. 
split; first by move=> go i ix; rewrite LgV //; apply: go.
move=> h y yx; move: (h _ yx); rewrite LgV //.
Qed.

Section OrderGraph.
Variables (x y g: Set).
Hypothesis (sr: substrate g = y).

Lemma order_graph_pr1:
  gfunctions x y = prod_of_substrates (cst_graph x g).
Proof. 
rewrite -cst_graph_pr /prod_of_substrates /fam_of_substrates /cst_graph.
aw; rewrite - sr; congr productb; apply: Lg_exten => v vs; rewrite LgV //.
Qed.

Lemma order_graph_pr:
  order_graph x y g = order_product (cst_graph x g).
Proof. 
rewrite /order_graph/order_product (order_graph_pr1) {2}/cst_graph.
rewrite /graph_on/order_product_r Lgd.
set_extens t => /Zo_P [t1 h]; apply /Zo_P;split =>// i ix;
                  move: (h _ ix); rewrite LgV //.
Qed. 

Lemma order_graph_osr: order g -> 
   order_on (order_graph x y g) (gfunctions x y).
Proof. 
move=> og; rewrite order_graph_pr =>//.
have [pa pb] := (order_product_osr (order_fam_cst og (x:=x))).
by split => //; rewrite order_graph_pr1.
Qed.

End OrderGraph.

(** Order on functions [x->y], induced by an order [r] on the target  *)

Definition order_function_r x y r f g :=
  [/\ function_prop f x y, function_prop g x y &
  forall i, inc i x -> gle r (Vf f i) (Vf g i)].

Definition order_function x y r :=
  graph_on (order_function_r x y r) (functions x y).


Section OrderFunction.
Variables (x y r: Set).
Hypothesis (or: order r) (sr: substrate r = y).

Lemma order_functionP f f': 
  gle (order_function x y r) f f' <->
  [/\ inc f (functions x y),
    inc f' (functions x y)  &
    forall i, inc i x -> gle r (Vf f i) (Vf f' i)].
Proof. 
split; first by move /Zo_P => [/setXp_P [pa pb]]; aw; move => [_ _ bb].
move => [pa pb pc];apply:Zo_i; first by apply:setXp_i. 
move/functionsP: pa => pa.
move/functionsP: pb => pb.
by hnf; aw.
Qed.

Lemma order_function_osr: order_on (order_function x y r)(functions x y).
Proof.
have gf: sgraph (order_function x y r) by apply: graph_on_graph.
have rr:forall u, inc u (functions x y) -> gle (order_function x y r) u u.
  move=> u us; apply: Zo_i; rewrite /coarse;fprops.
  aw; move /functionsP: us => [fu su tu].
  split => // i ix; order_tac.  
  rewrite sr -tu; rewrite - su in ix; fprops. 
have sr1: substrate (order_function x y r) = functions x y.
  set_extens t.
    by case/(substrate_P gf) => [] [z] /Zo_P [] /setXp_P [].
   by move => /rr/arg1_sr.
split => //; split.
      rewrite /order_function;apply: graph_on_graph. 
    by move=> z zs; apply: rr;rewrite - sr1.
  move=> a b c/order_functionP [afs bfs leab] /order_functionP [_ cfs lebc].
  apply/order_functionP;split=> //.
  move=> i id; move: (leab _ id) (lebc _ id) => lab lbc;  order_tac. 
move=> a b /order_functionP [afs bfs leab] /order_functionP [_ _ leba].
move: afs bfs => /functionsP [fa sa ta]  /functionsP [fb sb tb].
apply: function_exten=>//; try ue. 
rewrite sa; move=> i ix;move: (leab _ ix) (leba _ ix)=> lab lba; order_tac.
Qed.

(** The mapping that associates to a function its graph is an isomorphism 
  for the two orders defined above  *)

Lemma order_function_is: 
  order_isomorphism (Lf graph (functions x y)(gfunctions x y))
  (order_function x y r)(order_graph x y r).
Proof.
have [pa pb]:= order_function_osr.
have [pc pd] := order_graph_osr x sr or.
split => //; first by split; aw => //;apply: graph_fb.
have ax :=(graph_lf_axiom (x:=x) (y:=y)).
hnf; aw=> a b ass bss; rewrite ! LfV//; split.
  move/order_functionP => [_ _ h];apply:Zo_i;aw;trivial.
  by apply:setXp_i; apply: ax.
by move /Zo_hi;aw => xx; apply/order_functionP.
Qed.

Lemma order_function_is1: (order_function x y r) \Is (order_graph x y r).
Proof.
exists (Lf graph (functions x y) (gfunctions x y)).
by apply: order_function_is.
Qed.

End OrderFunction.

(** ** Increasing mappings *)

Definition increasing_fun f r r' :=
  [/\ order r, order r', function_prop f (substrate r) (substrate r')
   & fincr_prop f r r'].

Definition decreasing_fun f r r' :=
  [/\ order r, order r', function_prop f (substrate r) (substrate r')
  & forall x y,  gle r x y  -> gle r' (Vf f y) (Vf f x)].

Definition monotone_fun f r r' :=
  increasing_fun f r r' \/  decreasing_fun f r r'.

(** Monotonicity and opposite order *)

Lemma increasing_fun_reva  f r r':
   increasing_fun f r r' -> decreasing_fun f r (opp_order r').
Proof. 
rewrite /decreasing_fun=> [] [or or' [ff sr sr'] rel].
move: (opp_osr or') => [pa pb]; split => //.
  by saw;rewrite pb.
by move=> x y xy; apply/igraph_pP; apply: rel.
Qed.

Lemma increasing_fun_revb  f r r':
   increasing_fun f r r' -> decreasing_fun f (opp_order r) r'.
Proof. 
rewrite /decreasing_fun=> [] [or or' [ff sr sr'] rel].
move: (opp_osr or) => [pa pb]; split => //.
  by saw; rewrite pb.
by move=> x y /igraph_pP => xy;apply: rel.
Qed.

Lemma decreasing_fun_reva  f r r':
   decreasing_fun f r r' -> increasing_fun f r (opp_order r').
Proof. 
rewrite /increasing_fun=> [] [or or' [ff sr sr'] rel].
move: (opp_osr or') => [pa pb]; split => //.
   by saw; rewrite pb.
by move=> x y xy; apply/igraph_pP; apply: rel.
Qed.

Lemma decreasing_fun_revb  f r r':
   decreasing_fun f r r' -> increasing_fun f (opp_order r) r'.
Proof. 
rewrite /increasing_fun=> [] [or or' [ff sr sr'] rel].
move: (opp_osr or) => [pa pb]; split => //.
  by saw;rewrite pb.
by move=> x y /igraph_pP => xy;apply: rel.
Qed.

Lemma monotone_fun_reva  f r r':
   monotone_fun f r r' -> monotone_fun f r (opp_order r').
Proof.
case; first by right; apply: increasing_fun_reva.
by left; apply: decreasing_fun_reva.
Qed.

Lemma monotone_fun_revb f r r':
   monotone_fun f r r' -> monotone_fun f (opp_order r) r'.
Proof. 
case; first  by right; apply: increasing_fun_revb.
by left; apply: decreasing_fun_revb.
Qed.


Lemma increasing_compose f g r r' r'':
  increasing_fun f r r' ->  increasing_fun g r' r'' ->
  [/\ g \coP f,
    (forall x, inc x (source f) -> Vf (g \co f) x = Vf g (Vf f x)) 
    & increasing_fun (g \co f) r r''].
Proof.
move=>  [or or' [ff sf tf] icf][_ or'' [fg sg tg] icg].
have cgf: (g \coP f) by split => //; ue.  
have p:(forall x, inc x (source f) -> Vf (g \co f) x = Vf g (Vf f x)).
  move=> x xsf; rewrite compfV//.
split => //; split => //; first by saw; fct_tac.
move => x y xy.
have xsf: inc x (source f) by rewrite sf; order_tac.
have ysf: inc y (source f) by rewrite sf; order_tac.
by rewrite p // p //; apply: icg; apply: icf.
Qed.

(** Strict monotone functions *)

Definition strict_increasing_fun f r r' :=
  [/\ order r, order r', function_prop f (substrate r) (substrate r')
   & fsincr_prop f r r'].
Definition strict_decreasing_fun f r r' :=
  [/\ order r, order r', function_prop f (substrate r) (substrate r')
  & forall x y,  glt r x y  -> glt r' (Vf f y) (Vf f x)].

Definition strict_monotone_fun f r r' :=
  strict_increasing_fun f r r' \/  strict_decreasing_fun f r r'.

Lemma strict_increasing_fun_reva f r r':
  strict_increasing_fun f r r' -> strict_decreasing_fun f r (opp_order r').
Proof. 
rewrite /strict_decreasing_fun; move=> [or or' [ ff sr sr'] rel].
move: (opp_osr or') => [pa pb]; split => //; first by  saw; rewrite pb.
by move=> x y xy;apply /opp_gltP; apply: rel.
Qed.

Lemma strict_increasing_fun_revb f r r':
  strict_increasing_fun f r r' -> strict_decreasing_fun f (opp_order r) r'.
Proof.
rewrite /strict_decreasing_fun; move=> [or or' [ ff sr sr'] rel].
move: (opp_osr or) => [pa pb]; split => //; first by saw; ue.
by move=> x y /opp_gltP;apply: rel.
Qed.

Lemma strict_decreasing_fun_reva  f r r':
  strict_decreasing_fun f r r' -> strict_increasing_fun f r (opp_order r').
Proof.
rewrite/ strict_increasing_fun; move=> [or or' [ ff sr sr'] rel].
move: (opp_osr or') => [pa pb]; split => //; first by saw; ue.
by move=> x y xy; apply /opp_gltP; apply: rel.
Qed.

Lemma strict_decreasing_fun_revb  f r r':
  strict_decreasing_fun f r r' -> strict_increasing_fun f (opp_order r) r'.
Proof. 
rewrite/ strict_increasing_fun; move=> [or or' [ ff sr sr'] rel].
move: (opp_osr or) => [pa pb]; split => //; first by saw;rewrite pb.
move=> x y /opp_gltP; apply: rel.
Qed.

Lemma strict_monotone_fun_reva  f r r':
  strict_monotone_fun f r r' -> strict_monotone_fun f r (opp_order r').
Proof.
case; first by right; apply: strict_increasing_fun_reva.
by left; apply: strict_decreasing_fun_reva.
Qed.

Lemma strict_monotone_fun_revb f r r':
   strict_monotone_fun f r r' -> strict_monotone_fun f (opp_order r) r'.
Proof. 
case; first  by right; apply: strict_increasing_fun_revb.
by left; apply: strict_decreasing_fun_revb.
Qed.

Lemma strict_increasing_w f r r':
   strict_increasing_fun f r r' ->  increasing_fun f r r'.
Proof.
move=> [or or' [ ff sr sr'] rel]; split => // x y h. 
case: (equal_or_not x y) => xy.
  rewrite - xy; order_tac; rewrite - sr'; Wtac; rewrite sr; order_tac.
exact: (proj1 (rel _ _ (conj h xy))).
Qed.

Lemma strict_decreasing_w f r r':
   strict_decreasing_fun f r r' ->  decreasing_fun f r r'.
Proof.
move=> [or or' [ ff sr sr'] rel]; split => // x y h. 
case: (equal_or_not x y) => xy.
  rewrite - xy; order_tac; rewrite - sr'; Wtac; rewrite sr; order_tac.
exact: (proj1 (rel _ _ (conj h xy))).
Qed.



Lemma increasing_compose3 f g h r r' r'' r''':
  strict_increasing_fun f r r' ->  increasing_fun g r' r'' ->
  strict_increasing_fun h r'' r''' ->
  let res:= (h \co g) \co f in 
    [/\ inc res (functions (source f) (target h)),
      (forall x, inc x (source f) -> Vf res x = Vf h (Vf g(Vf f x))) &
      increasing_fun res r r'''].
Proof. 
move=>  sif ig sih.
have icf:= (strict_increasing_w sif).
have ich:= (strict_increasing_w sih).
have [chg Whg igh] := (increasing_compose ig ich).
have [chgf Whgf ighf] := (increasing_compose icf igh).
move=> res; rewrite /res;split => //.
  apply /functionsP; saw; fct_tac. 
move=> x xsf; rewrite ! compfV//.
move: (increasing_compose icf ig) => [[_ ff sgtf] _ _];Wtac.
Qed.

Lemma strict_increasing_compose3 f g h r r' r'' r''':
  strict_increasing_fun f r r' ->  strict_increasing_fun g r' r'' ->
  strict_increasing_fun h r'' r''' ->
  let res:= (h \co g) \co f in 
    [/\ inc res (functions (source f) (target h)),
      (forall x, inc x (source f) -> Vf res x = Vf h (Vf g(Vf f x))) &
      strict_increasing_fun res r r'''].
Proof. 
move=>  sif sig sih.
have icf:= (strict_increasing_w sif).
have ich:= (strict_increasing_w sih).
have ig:= (strict_increasing_w sig).
have [chg Whg igh] := (increasing_compose ig ich).
have [chgf Whgf ighf] := (increasing_compose icf igh).
have aux x: inc x (source f) -> Vf ((h \co g) \co f) x = Vf h (Vf g (Vf f x)).
  move => xsf; rewrite !compfV //.
  move: (increasing_compose icf ig) => [[_ ff sgtf] _ _];Wtac.
move=> res; rewrite /res;split => //.
  apply /functionsP; saw; fct_tac.
move: ighf =>[qa qb qc qd]; split => // x y lxy.
move: (arg1_sr (proj1 lxy)) (arg2_sr (proj1 lxy)).
rewrite - (proj32 (proj43 sif)) => xsf ysf; rewrite !aux => //.
by apply: (proj44 sih); apply: (proj44 sig); apply: (proj44 sif).
Qed.

Lemma order_morphism_increasing f r r':
  order_morphism f r r' ->
  strict_increasing_fun f r r'.
Proof.
move => h; move: (order_morphism_sincr h) => si.
move:h=> [or or' [ ff sr sr'] rel]; split => //.
Qed.

Lemma order_isomorphism_increasing f r r':
  order_isomorphism f r r' ->
  strict_increasing_fun f r r'.
Proof. 
move => h; apply order_morphism_increasing. 
by apply order_isomorphism_w.
Qed.


(** Example of monotone functions. *)

Lemma constant_fun_increasing f r r':
  order r -> order r' -> substrate r = source f  ->
  substrate r' = target f -> constantfp f ->
  increasing_fun f r r' /\ decreasing_fun f r r'.
Proof. 
move=> or or' sr sr' [ff cf].
split; split => // x y rxy; move:(arg1_sr rxy)(arg2_sr rxy);
  rewrite sr => xs ys; rewrite (cf _ _ xs ys); order_tac; ue.
Qed.

Lemma identity_increasing_decreasing  x (r := diagonal x) :
  (increasing_fun (identity x) r r /\ decreasing_fun (identity x) r r).
Proof. 
have [oi si]:= (diagonal_osr x).
move:(identity_prop (substrate r)); rewrite {1} si => pa.
split;split => // a b rab; rewrite !idV //;try (rewrite - si; order_tac).
by move/diagonal_pi_P: rab => [ax <-]; apply/diagonal_pi_P.
Qed.
 
Lemma setC_decreasing E:
  strict_decreasing_fun (Lf (complement E)(\Po E)(\Po E))
  (subp_order E) (subp_order E).
Proof.
move: (subp_osr E); set (r:=sub_order E); move => [or sr].
have ta: lf_axiom (complement E) (\Po E) (\Po E).
   move=> c cE;apply/setP_P; apply: sub_setC.
split => //; first by hnf; aw; split => //; apply: lf_function.
move=> x y [] /subp_gleP [xE yE xy] nxy. 
rewrite !LfV //; try (apply/setP_P => //); split.
  apply/subp_gleP;split; try (apply:sub_setC);  by apply /(set_CSm xE yE).
dneg cc; move:(f_equal (complement E) cc).
by rewrite (setC_K yE) (setC_K xE).
Qed.

Lemma setC_isomorphism E:
  order_isomorphism (Lf (complement E)(\Po E)(\Po E))
  (subp_order E) (opp_order (subp_order E)).
Proof.
move: (subp_osr E); set (r:=sub_order E); move => [or sr].
case: (opp_osr or); rewrite sr => or' sr'.
have ta: lf_axiom (complement E) (\Po E) (\Po E).
   move=> c cE;apply/setP_P; apply: sub_setC.
split => //.
  hnf; aw; split => //; apply:lf_bijective => //.
    by move => u v /setP_P /setC_K {2} <- /setP_P /setC_K {2} <- ->.
  move => y /setP_P yE; exists (E -s y); last by rewrite setC_K.
  apply /setP_P; apply: sub_setC.
hnf;aw => x y xE yE; rewrite !LfV//.
  move: xE yE => /setP_P xE /setP_P yE; split.
  move/subp_gleP => [_ _ /(set_CSm xE yE) h].
  apply/opp_gleP /subp_gleP; split =>//; apply: sub_setC.
by move => /opp_gleP /subp_gleP [_ _ /(set_CSm xE yE) h]; apply/subp_gleP.
Qed.


(** If [M x] is the set of upper bounds of [x] then [M] is striclty decreasing in the power set *)

Definition upper_bounds1 r x :=
  Zo (substrate r)(fun y => gle r x y).

Lemma upper_bounds1_P x y r:
  order r -> inc x (substrate r) -> inc y (substrate r) ->
  (gle r x y <-> sub (upper_bounds1 r y) (upper_bounds1 r x)).
Proof.
rewrite /upper_bounds1 => or xs ys;split.
  move=> lexy t /Zo_P [ts yt]; apply :Zo_i => //;order_tac.
set s:= Zo _ _; move=> ss.
have yss: inc y s by rewrite /s Zo_P; split => //; order_tac.
by move /Zo_P: (ss _ yss)=> []. 
Qed.

Lemma upper_bounds1_decreasing r:
  order r ->
  strict_decreasing_fun 
    (Lf (upper_bounds1 r) (substrate r)(\Po (substrate r))) 
    r (subp_order (substrate r)).
Proof.
move=> or; hnf; aw; aw.
set E:= substrate r.
have [oe si] :=(subp_osr E).
have ta: lf_axiom (upper_bounds1 r) E (\Po E).
  by move=> x xE; apply /setP_P => t /Zo_P []. 
split => //.
  by rewrite si;saw; apply: lf_function. 
move => x y ltxy.
have xE: inc x E by rewrite /E;order_tac. 
have yE: inc y E by rewrite /E;order_tac.
have [lexy nxy] := ltxy.
move:(lexy) => /(upper_bounds1_P or xE yE) sxy.
rewrite !LfV //; split.
  apply /subp_gleP;split => //.
  by move: (ta _ yE) =>/setP_P.
  by move: (ta _ xE) =>/setP_P.
dneg seq.
suff: gle r y x  by move => le; order_tac.
by apply/(upper_bounds1_P or yE xE) ;rewrite seq; fprops.
Qed.

(** comparison of monotone and morphism *)

Lemma strict_increasing_from_injective f r r':
  injection f -> increasing_fun f r r' -> strict_increasing_fun f r r'.
Proof. 
move=> [_ inf] [or or' [ ff sr sr'] rel]; split => //.
move=> x y [lexy neq]; split; first by apply: rel.
dneg Wxy; apply: inf=>//; rewrite sr; order_tac. 
Qed.

Lemma strict_decreasing_from_injective f r r':
  injection f -> decreasing_fun f r r' -> strict_decreasing_fun f r r'.
Proof. 
move=> [_ inf] [or or' [ ff sr sr'] rel]; split => //.
move=> x y [lexy neq]; split; first by apply: rel.
dneg Wxy; apply: inf=>//; rewrite sr; order_tac. 
Qed.

Lemma strict_monotone_from_injective f r r':
  injection f -> monotone_fun f r r' -> strict_monotone_fun f r r'.
Proof.
move=> inf; case.
  by left; apply: strict_increasing_from_injective.
by right; apply: strict_decreasing_from_injective.
Qed.

Lemma order_isomorphism_P f r r':
  order r -> order r' ->  
  bijection f ->  substrate r = source f -> substrate r' = target f  ->
  (order_isomorphism f r r' <->
    (increasing_fun f r r' /\ increasing_fun (inverse_fun f) r' r)).
Proof.
move=> or or' bf sr sr'.
move: (bijective_inv_f bf)=> bif.
have sf: source f = target (inverse_fun f) by rewrite /inverse_fun; aw.
have tf: target f = source (inverse_fun f) by rewrite /inverse_fun; aw.
split.
  move => h; move:(order_isomorphism_incr h) => h2.
  split; saw. 
  - split=> //; fct_tac.
  - split; aw  => //; fct_tac.
  - move=>x y rxy.
    have xt: inc x (target f) by rewrite - sr'; order_tac.
    have yt: inc y (target f) by rewrite - sr'; order_tac.
    by apply /(proj44 h); try Wtac; rewrite (inverse_V bf xt) (inverse_V bf yt).
move=> [inf inif]; hnf; split => // x y xsf ysf.
split; first by move=> hy;  apply: (proj44 inf).
move=> hyp.
rewrite  - (inverse_V2 bf xsf) - (inverse_V2 bf ysf).
by apply: (proj44 inif).
Qed.


Lemma order_isomorphism_opposite g r r':
  order_isomorphism g r r' ->
  order_isomorphism g (opp_order r) (opp_order r').
Proof. 
rewrite /order_isomorphism; move=> [pa pb [pc pd pe] pf].
move: (opp_osr pa) (opp_osr pb) => [qa qb] [qc qd].
split => //; first by split => //; ue.
move => x y xsg ysg.
transitivity (gle r y x) ; first by apply /igraph_pP.
transitivity (gle r' (Vf g y) (Vf g x)); first by apply/(pf _ _ ysg xsg).
symmetry; apply /igraph_pP.
Qed.

(** We have [u v u = u] and [v u v = v] if  [u] and [v] are decreasing, 
  [v (u(x)) ] and [u(v(x))] are both [ => x] *)  

Theorem decreasing_composition u v r r':
  decreasing_fun u r r' -> decreasing_fun v r' r ->
  (forall x, inc x (substrate r) -> gle r (Vf v (Vf u x)) x) ->
  (forall x', inc x' (substrate r') -> gle r' (Vf u (Vf v x')) x') ->
  (u \co v \co u = u /\ v \co  u \co v = v).
Proof.
move=>  [or or' [fu sr sr'] du] [_ _ [fv svr svr'] dv] h h'.
have cvu: v \coP u by split => //; ue.
have fvu: function (v \co u) by fct_tac. 
have cuv: u \coP v by split => //; ue.
have fuv: function (u \co v) by fct_tac. 
have cuvu: (u \co v) \coP u by split => //; aw; ue.
have cvuv:  (v \co u) \coP v by split => //; aw; ue.
split.
  apply: function_exten; aw; trivial;first by fct_tac. 
  move=> x xs. 
  rewrite sr in xs; move:(h _ xs)=> rel1; move: (du _ _ rel1)=> rel2.
  have p: inc (Vf u x)(substrate r') by rewrite - sr';Wtac.
  move: (h' _ p)=> rel3; rewrite !compfV //; try ue.
  order_tac.
apply: function_exten; aw; trivial; first by fct_tac. 
move=> x xs.
rewrite svr in xs; move:(h' _ xs)=> rel1; move: (dv _ _ rel1)=> rel2.
have p: inc (Vf v x) (substrate r) by rewrite - svr';Wtac.
move: (h _ p)=> rel3; rewrite !compfV //; try ue.
order_tac. 
Qed.

(** ** Maximal and minimal elements *)


Definition maximal r a :=
  inc a (substrate r) /\ forall x, gle r a x -> x = a.
Definition minimal r a :=
  inc a (substrate r) /\ forall x, gle r x a -> x = a.


Lemma maximal_opp r: order r -> forall x,
   (maximal (opp_order r) x <-> minimal r x).
Proof.
move=> or x; rewrite /maximal /minimal (proj2 (opp_osr or)); split;
  move => [xsr h]; split=> // y /igraph_pP;apply: h.
Qed.

Lemma minimal_opp r: order r -> forall x,
   (minimal (opp_order r) x <-> maximal r x).
Proof.
move=> or x; rewrite /maximal /minimal (proj2 (opp_osr or)); split;
  move => [xsr h]; split=> // y /igraph_pP;apply: h.
Qed.

(** Example: For inclusion, the empty set is least; 
 if excluded, singletons become minimal *)

Lemma minimal_inclusion E y (F:= (\Po E) -s1 emptyset):
  inc y F -> (minimal (sub_order F) y <-> singletonp y).
Proof. 
move=> yF.
rewrite/minimal (proj2 (sub_osr F)).
have Fp x:  inc x F <-> (sub x E /\ nonempty x).
  split.
    by move/setC1_P => [] /setP_P pa /nonemptyP nw. 
  by move => [pa /nonemptyP pb]; apply/setC1_P; split=> //; apply/setP_P.
split.
  move => [/Fp [yE [z zy]] sp].
  have aux: sub (singleton z) y by apply:set1_sub.
  have stF: inc (singleton z) F.
    apply /Fp; split; [ apply: sub_trans aux yE  | apply: set1_ne].
  by exists z; symmetry; apply: sp;apply/graph_on_P1.
move=> /singletonP [_ hyp]; split => // x /graph_on_P1 [/Fp [xE [t tx]] _ xy].
apply: extensionality=>//.
by move: (xy _ tx)=> ty z zy; rewrite - (hyp _ _ ty zy).
Qed.

(** Maximal partial functions for extension order are total functions*)

Lemma maximal_extensionP E F x:
  nonempty F -> inc x (sub_functions E F) ->
  (maximal (opp_order (extension_order E F)) x <-> (source x = E)).
Proof. 
have [eo es]:= (extension_osr E F).
move=> [t tF] xs; apply: (iff_trans (maximal_opp eo _)).
split.
  move: (xs) => /sfunctionsP [fx sx tx][_ h].
  apply: extensionality=>// y yE. 
  ex_middle yns.
  have aux: gle (extension_order E F) (extension x y t) x.
    rewrite /extension;apply /extension_order_P1; split=> //;last by aw; fprops.
    apply /sfunctionsP; split => //; aw.
    - apply: extension_f => //.
    - by move => z /setU1_P; case; [apply: sx |move=>->].
    - rewrite - tx; apply /setU2id_Pr => s /set1_P ->; ue.
  by rewrite -(h _ aux); rewrite /extension; aw; fprops.
move=> sx.
hnf; aw; split; first by ue.
move=> y /extension_orderP [ys _ et].
move: xs ys => /sfunctionsP [fx _ tx]  /sfunctionsP [fy sy ty].
have sy' := (extends_Ssource et).
symmetry;apply: function_exten=>//; try ue.
  apply: extensionality=>//; ue. 
move=> z zs /=; apply: (extends_sV et zs). 
Qed.

(** ** Greatest element and least element *)

Definition greatest r a :=
  inc a (substrate r) /\ forall x, inc x (substrate r) -> gle r x a.
Definition least r a :=
  inc a (substrate r) /\ forall x, inc x (substrate r) -> gle r a x.

Definition the_least r := select (least r) (substrate r).
Definition the_greatest r := select (greatest r) (substrate r).
Definition has_least r := (exists u, least r u).
Definition has_greatest r := (exists u, greatest r u).

Section GreatestProperties.
Variable (r: Set).
Hypothesis (or: order r).


Lemma unique_greatest : uniqueness (greatest r).
Proof. 
move=> a b [asr h] [bsr bh]. 
apply: (order_antisymmetry or (bh _ asr) (h _ bsr)).
Qed.

Lemma unique_least: uniqueness (least r).
Proof.
move=> a b [asr h] [bsr bh]. 
apply: (order_antisymmetry or (h _ bsr) (bh _ asr)).
Qed.

Lemma the_least_pr: has_least r -> least r (the_least r).
Proof.  
rewrite /the_least=> h; apply: (proj1(select_pr _ _)).
  by move: h => [z zl];exists z => //; move: zl => [ok _].
by move => x y xsr xlt yset ylt; apply: unique_least.
Qed.

Lemma the_greatest_pr: has_greatest r -> greatest r (the_greatest r).
Proof. 
rewrite /the_greatest=> h; apply:  (proj1(select_pr _ _)).
  by move: h => [z zl]; exists z => //;  move: zl => [ok _].
by move => x y xsr xlt ysr ylt; apply: unique_greatest.
Qed.

Lemma the_least_pr2 x: least r x -> the_least r = x.
Proof. 
move=> le. 
have exu: has_least r by exists x. 
exact: (unique_least (the_least_pr exu) le). 
Qed.

Lemma the_greatest_pr2 x: greatest r x -> the_greatest r = x.
Proof.
move=> le. 
have exu: has_greatest r by exists x. 
exact: (unique_greatest (the_greatest_pr exu) le).
Qed.

Lemma least_and_greatest x: least r x -> greatest r x ->
  singletonp (substrate r).
Proof. 
move => [xs lex][_ gex]; exists x.
apply: (set1_pr xs) => z zs; move: (lex _ zs)(gex _ zs)=> xy yx.
order_tac.
Qed.

Lemma least_minimal a: least r a -> minimal r a.
Proof. 
move=>  [asr h]; split=>// x ax;move: (h _ (arg1_sr ax)) => xa; order_tac.
Qed.


Lemma greatest_maximal a: greatest r a -> maximal r a.
Proof. 
move=> [asr h]; split=>// x ax;move: (h _ (arg2_sr ax)) => xa; order_tac.
Qed.

End GreatestProperties.


Lemma greatest_of_induced r s x: 
  order r -> sub s (substrate r) -> inc x s ->
  greatest r x ->
  the_greatest r = the_greatest (induced_order r s).
Proof. 
move=> or ssr xs grx.
have [pa pb] :=(iorder_osr or ssr).
rewrite (the_greatest_pr2 or grx).
symmetry; apply: the_greatest_pr2 => //.
hnf; rewrite pb; split => //.
by move => y yxs; apply/iorder_gle0P=> //;apply (proj2 grx); apply: ssr.
Qed.

Definition the_least_induced r x := the_least (induced_order r x).

Lemma least_of_induced r s x:
  order r -> sub s (substrate r) -> inc x s ->
  least r x ->
  the_least r = the_least_induced r s.
Proof.
move=> or ssr xs grx.
move: (iorder_osr or ssr) => [pa pb].
rewrite (the_least_pr2 or grx). 
symmetry; apply: the_least_pr2 => //.
hnf; rewrite /the_least_induced pb; split => //. 
by move => y yxs; apply/iorder_gle0P => //;apply (proj2 grx); apply: ssr.
Qed.

Lemma greatest_opposite a r:
  order r -> greatest r a -> least (opp_order r) a.
Proof. 
by move=> /opp_osr [_ pb] [asr hy]; split; rewrite pb // => x /hy /igraph_pP.
Qed.

Lemma least_opposite a r:
  order r -> least r a -> greatest (opp_order r) a.
Proof.
by move=> /opp_osr [_ pb] [asr hy]; split; rewrite pb // => x /hy /igraph_pP.
Qed.

Lemma the_least_opposite r: order r ->
  has_greatest r ->
  the_least (opp_order r) =  the_greatest r.
Proof. 
move=> or /(the_greatest_pr or) /(greatest_opposite or) hy.
apply: the_least_pr2 => //; apply: (proj1 (opp_osr or)).
Qed.

Lemma the_greatest_opposite r: order r ->
  has_least r ->
  the_greatest (opp_order r) =  the_least r.
Proof. 
move=> or /(the_least_pr or) /(least_opposite or) hy.
apply: the_greatest_pr2 => //; apply: (proj1 (opp_osr or)).
Qed.

Lemma greatest_unique_maximal a b r:
  greatest r a -> maximal r b -> a = b.
Proof. by move=> [ar ha][br hb]; apply: hb; apply: ha. Qed.

Lemma least_unique_minimal a b r:
  least r a -> minimal r b -> a = b.
Proof.
by move=> [ar ha][br hb]; apply: hb; apply: ha. 
Qed.

(** Examples: subinclusion  *)

Lemma least_is_setI s a:
  least (sub_order s) a -> a = intersection s.
Proof.
rewrite /least;move: (sub_osr s) => [_ ->] [asr h].
set_extens x => xs; last by apply: setI_hi xs asr.
apply: setI_i =>//; first by exists a.
by move => y ys; move: (h _ ys) => /graph_on_P1 [_ _ ]; apply.
Qed.

Lemma greatest_is_setU s a:
  greatest (sub_order s) a ->  a = union s.
Proof.
rewrite /greatest; move :(sub_osr s) => [_ ->] [asr h].
set_extens x =>  xs;first by union_tac.
by move: (setU_hi xs)=> [y xy ys];move: (h _ ys) => /graph_on_P1 [_ _]; apply. 
Qed.

Lemma setI_least s:
  inc (intersection s) s ->
  least (sub_order s) (intersection s) . 
Proof. 
move=> iis;hnf; rewrite (proj2 (sub_osr s)); split => //.
by move => x xs;apply/graph_on_P1;split => //; apply: setI_s1.
Qed.

Lemma setU_greatest s:
  inc (union s) s -> greatest (sub_order s) (union s). 
Proof.
move=> iis;hnf; rewrite (proj2 (sub_osr s)); split => //.
by move=> x xs;apply/graph_on_P1;saw; apply: setU_s1.
Qed.

(** example: inclusion on the powerset *)

Lemma emptyset_least E:
  least (subp_order E) emptyset. 
Proof.
have eP := (setP_0i E).
move/sub_set0:(setI_s1 eP) => h.
by rewrite -h;apply: setI_least; rewrite h.
Qed.

Lemma wholeset_greatest E:
  greatest (subp_order E) E. 
Proof. 
have aux: inc E (\Po E) by apply: setP_Ti.
have h: union (\Po E) = E.
  apply:extensionality;last by apply:(setU_s1 aux).
  by apply:setU_s2 => y /setP_P.
by rewrite -{2} h; apply:setU_greatest; rewrite h.
Qed.

(** The least function for extension is the empty function; 
there is generally no greatest *)

Lemma least_extension E F:
  least (opp_order (extension_order E F)) (empty_function_tg F).
Proof. 
have [or sr] :=(extension_osr E F).
hnf;move: (opp_osr or) => [or' ->]; rewrite sr.
have p1:inc (empty_function_tg F) (sub_functions E F).
  have [pa pb pc] := (empty_function_tg_function F).
  apply/sfunctionsP; split => //; rewrite pb; fprops.
split=>// x xs; apply/igraph_pP /extension_order_P1; split => //.
rewrite empty_function_graph; fprops.
Qed.

Lemma greatest_extension E F x:
  greatest (opp_order (extension_order E F)) x ->
  nonempty E -> small_set F.
Proof. 
move=> ge [t tE].
case: (emptyset_dichot F); first by move => ->; exact: small0.
have [oe sr] :=(extension_osr E F).
case: (opp_osr oe); set (r:= opp_order (extension_order E F)) => or sr' neF.
have alc u: inc u F -> Vf x t = u.
  move=> uF.
  move: (constant_prop E uF) => [sa sb sc].
  have fsf:inc (constant_function E F u) (sub_functions E F). 
    apply /sfunctionsP;split => //. by rewrite sb.
  move/(maximal_extensionP neF fsf): sb => sF.
  by rewrite (greatest_unique_maximal ge sF) constant_V.
by move => u v /alc <- /alc <-.
Qed.

(** If [X] is a set whose elements are reflexive in [E] and
  if the diagonal of [E] is in [X], then it is the least element of [X] 
  ordered by inclusion, thanks to the next lemma.
*)

Lemma least_equivalence r:
  reflexivep r -> sub (diagonal (substrate r)) r.
Proof. 
by move=> rr t /diagonal_i_P [pt Ps PQ]; rewrite -pt -PQ; apply: rr.
Qed.

(** If [f:E->F] is a bijection, [r] an ordering on [E], there is a unique 
  ordering on [F] that makes [f] an isomorphism *) 

Lemma order_transportation f r (r':= Vfs (f \ftimes f) r) :
  bijection f -> order_on r (source f) ->
  order_isomorphism f r r'.
Proof. 
move=> [[ff injf] [_ sjf]] [or sr].
have gr: sgraph r by fprops.
have ffp: function_prop f (substrate r) (target f) by rewrite sr.
move:(ext_to_prod_fun_bis ffp ffp) => [fe se te].
have aux: sub r (source (ext_to_prod f f)).
  by rewrite se; apply:sub_graph_coarse_substrate. 
set (E:= source f).
have zr': (forall z,inc z r' <-> (exists x y, [/\ inc x E, inc y E,
    inc (J x y) r & z = J (Vf f x) (Vf f y)])).
  move => z; rewrite /r'; split.
    move /(Vf_image_P fe aux) => [x xr].
    move:(pr1_sr xr)(pr2_sr xr); rewrite sr => pxs pys.
    have Jg := (gr _ xr).
    rewrite  -Jg (ext_to_prod_V ff ff  pxs pys) => ->.
    by exists (P x), (Q x); rewrite Jg. 
  move=> [x [y [xE yE Jr zJ]]]; apply /(Vf_image_P fe aux); ex_tac.
  move:(arg1_sr Jr)(arg2_sr Jr); rewrite sr => xs ys.
  by rewrite (ext_to_prod_V ff ff xs ys).
have gr': sgraph r' by move=> z /zr'; move=> [x [y [_ _ _ ->]]]; fprops.
have sr': substrate r' = target f.
  set_extens t.
  + case /(substrate_P gr') => [] [y] /zr'[u [v [uE vE Jr zJ]]].
       by rewrite  (pr1_def zJ); fprops. 
     by rewrite  (pr2_def zJ); fprops.
  +  move/sjf => [x xsf Wt].
    apply: (@arg1_sr _ t t); apply/ zr'; exists x; exists x. 
   rewrite Wt; split=> //; order_tac; ue.
suff or': order r'.
  hnf;split => // x y xsr ysr; split.
    by move =>h;apply /zr'; exists x, y.
  move/zr' => [x' [y' [xE' yE' pr sj]]].
  move: (pr12_def sj) => [w1 w2].
  by rewrite (injf _ _ xsr xE' w1)(injf _ _ ysr yE' w2).
split; first exact.
- move => y;rewrite sr' => yr; apply/zr'. 
  move: (sjf _ yr) => [x xsf Wt]. 
  exists x, x; rewrite Wt; split => //; order_tac; ue.
- move=>x y z /zr' [a [b [aE bE J1r Jab]]] /zr' [c [d [cE dE J2r Jcd]]].
  apply/zr'; exists a, d.
  have bc: (b = c).
    by apply: injf =>//;rewrite - (pr2_def Jab) - (pr1_def Jcd).
  rewrite bc in J1r.
  by rewrite - (pr1_def Jab)- (pr2_def Jcd); split => //; order_tac.
- move=> x y  /zr' [a [b [aE bE J1r Jab]]] /zr' [c [d [cE dE J2r Jcd]]].
  move:(pr12_def Jab) (pr12_def Jcd)=> [xva yvb][yvc xvd].
  have Wbc: Vf f b = Vf f c by rewrite - yvb.
  have Wad: Vf f a = Vf f d by rewrite - xva.
  move:(injf _ _ bE cE Wbc)  (injf _ _ aE dE Wad) => eq1 eq2.
  rewrite xva yvc.
  have -> // : c = d by rewrite eq1 eq2 in J1r; order_tac.
Qed.

(** Any ordered set can be extended by adjoining a greatest element *)

Definition order_with_greatest r a  :=
  r \cup (((substrate r) +s1 a) *s1 a).

Lemma order_with_greatest_pr r a (r':=order_with_greatest r a):
    order r ->  ~ (inc a (substrate r)) ->
    [/\ order_on r' ((substrate r) +s1 a),
      r = induced_order r' (substrate r) & greatest r' a].
Proof.
rewrite /r' /order_with_greatest => or nas {r'}.
set r':= union2 r _.
have jaa: inc (J a a) (((substrate r) +s1 a) *s1 a) by apply:indexed_pi; fprops.
have src:= (sub_graph_coarse_substrate (proj41 or)).
have gr': sgraph r' by rewrite  /r'/indexed; apply: setU2_graph; fprops. 
have sr': substrate r'= (substrate r) +s1 a.
  set_extens x. 
    move =>t; apply/setU1_P.
    case /(substrate_P gr'):t => [][y] /setU2_P [];
      try (left; substr_tac); move/setXp_P => [];
     [by move/setU1_P |  by move => _ /set1_P => h;right].
  case /setU1_P => hh; apply: (@arg1_sr _ x x).  
    by apply:setU2_1; order_tac.
  by rewrite hh; apply:setU2_2.
have rr: reflexivep r'.
  move => y;rewrite sr';case /setU1_P.   
    by move=> hyp;apply:setU2_1; order_tac.
  move=> ->;apply:setU2_2; fprops.
have tr:transitivep r'.
  move=> x y z;case /setU2_P=> h; case /setU2_P=> h'.
  + apply:setU2_1; order_tac.
  + apply:setU2_2; apply/setXp_P; move/setXp_P: h' => [pa pb];split => //.
    apply:setU2_1; substr_tac.
  + move/setXp_P: h => [pa pb]; case: nas; move/set1_P: pb => <-; substr_tac.
  + move/setXp_P: h' => [_] /set1_P ->; move/setXp_P: h => [pb] _. 
    by apply:setU2_2; apply: indexed_pi.
have ar:antisymmetricp r'. 
  move=> x y;case /setU2_P=> h; case /setU2_P=> h'. 
  + order_tac.
  + case: nas; move/setXp_P: h' => [_] /set1_P <-; substr_tac.
  + case: nas; move/setXp_P: h => [_] /set1_P <-; substr_tac.
  + by move/setXp_P: h => [_] /set1_P ->;  move/setXp_P: h' => [_] /set1_P ->.
have or': order r' by [].
split => //.
  rewrite /r' /induced_order; set_extens x =>  xr.
    by apply: setI2_i; [  apply/setU2_P; left| apply: src].
  case/setI2_P: xr => /setU2_P [] //.
  by move /setX_P => [_ _] /set1_P qa /setX_P [_ _]; rewrite qa.
hnf; rewrite sr'; split; fprops.
by move=> x xe; apply /setU2_P; right; apply: indexed_pi.
Qed.

Theorem adjoin_greatest r a E:
  order_on r E -> ~ (inc a E) ->
  exists !r', [/\ order_on r' (E +s1 a),
    r = induced_order r' E & greatest r' a].
Proof. 
move=> [or sr] naE.
set (E':=E +s1 a).
set (r':=r \cup (E' \times (singleton a))).
apply /unique_existence; split.
  exists  (order_with_greatest r a).
  rewrite - sr in naE; move: (order_with_greatest_pr or naE); ue.
pose p x := [/\ order_on x E', r = x \cap (coarse E) & greatest x a].
suff : forall x y, p x -> p y -> sub x y.
  move=> hyp x y px py.
  apply: extensionality; [ apply: hyp px py | apply: hyp py px].
move=> x y [[ox sx] ix gx] [[oy sy] iy gy] z zx.
have pz:=(proj41 ox _ zx).
move: (pr1_sr zx)(pr2_sr zx); rewrite  sx => PzE QzE.
case/setU1_P: PzE=> Pz.
  case /setU1_P: QzE=> Qz.
    have: (inc z r) by rewrite ix;apply: setI2_i=> //; apply /setX_P. 
    by rewrite iy; move /setI2_P => [].
  move: gy=>[ay ga];rewrite -pz Qz; apply: ga; rewrite sy /E'; fprops.
case /setU1_P: QzE => Qz.
  have rel2 : gle x (Q z) (P z).
    move: gx=>[ax ga]; rewrite Pz; apply: ga; rewrite sx /E'; fprops.
  move: zx; rewrite -{1} pz. rewrite -/(related  _ _ _) -/(gle _ _ _)=> rel1.
  have PQ: P z = Q z by order_tac.
  by case: naE; rewrite -Pz PQ.
rewrite -pz Qz; move: gy=>[ax]; apply; ue.
Qed.

(** A set [A] is cofinal (resp. coinitial) if every element of [E] is bounded 
above (resp. below) by an element of [A]   *) 

Definition cofinal r a :=
  sub a (substrate r) /\ 
  (forall x, inc x (substrate r) -> exists2 y, inc y a & gle r x y).

Definition coinitial r a :=
  sub a (substrate r) /\ 
  (forall x, inc x (substrate r) -> exists2 y, inc y a & gle r y x).

Lemma exists_greatest_cofinalP r:
  (has_greatest r) <->
  (exists2 a, cofinal r a & singletonp a).
Proof. 
split. 
  move=> [a [asr h]]; exists (singleton a); last by exists a.
    split; [by move=> t /set1_P -> | move=> x xr; exists a;fprops].
move=> [a [asr h] [b bp]];exists b;split. 
  apply: asr; rewrite bp; fprops.
by move=> x xsr; move:(h _ xsr)=> [y]; rewrite bp; move /set1_P => ->.
Qed.

Lemma exists_least_coinitialP r:
  (has_least r) <->
  (exists2 a, coinitial r a & singletonp a).
Proof. 
split. 
  move=> [a [asr h]]; exists (singleton a); last by exists a.
  split; [ by move=> t /set1_P -> | move=> x xr; exists a; fprops ].
move=> [a [asr h] [b bp]];exists b;split. 
  apply: asr; rewrite bp; fprops.
by move=> x xsr; move:(h _ xsr)=> [y]; rewrite bp; move /set1_P => ->.
Qed.

(** ** Upper and lower bounds *)

Definition upper_bound r X x :=
  inc x (substrate r) /\ forall y, inc y X -> gle r y x.
Definition lower_bound r X x :=
  inc x (substrate r) /\ forall y, inc y X -> gle r x y.

Lemma opposite_upper_boundP r: order r -> forall X x,
  (upper_bound r X x <-> lower_bound (opp_order r) X x).
Proof. 
rewrite /upper_bound/lower_bound=> or X; rewrite (proj2 (opp_osr or)).
by split; move=> [xsr h]; split=>//; move=> y yR; move:(h _ yR); move/igraph_pP.
Qed.

Lemma opposite_lower_boundP r: order r -> forall X x,
  (lower_bound r X x <-> upper_bound  (opp_order r) X x).
Proof. 
rewrite /upper_bound/lower_bound=> or X x; rewrite (proj2 (opp_osr or)).
by split; move=> [xsr h]; split=>//; move=> y yR; move:(h _ yR); move/igraph_pP.
Qed.

Lemma smaller_lower_bound x y X r: preorder r ->
  lower_bound r X x -> gle r y x -> lower_bound r X y.
Proof. 
rewrite /lower_bound=> [] [rr _ tr] [xH h] yx.
split; first by order_tac.
move=> z zX; apply: tr yx (h _ zX).
Qed.

Lemma greater_upper_bound  x y X r: preorder r ->
  upper_bound r X x -> gle r x y -> upper_bound r X y.
Proof.
rewrite /lower_bound=> [] [rr _ tr] [xH h] yx.
split; first order_tac.
move=> z zX; apply: tr (h _ zX) yx.
Qed.

Lemma sub_lower_bound x X Y r: 
  lower_bound r X x -> sub Y X -> lower_bound r Y x.
Proof. 
rewrite /lower_bound=> [] [xR lo] YX.
split=>//; move=> y yY; apply: lo (YX _ yY).
Qed.

Lemma sub_upper_bound x X Y r:
  upper_bound r X x -> sub Y X -> upper_bound r Y x.
Proof. 
rewrite /lower_bound=> [] [xR lo] YX.
split=>//; move=> y yY; apply: lo (YX _ yY).
Qed.

Lemma least_elementP X r: order r -> sub X (substrate r) ->
  (has_least (induced_order r X) <->
  (exists2 x, lower_bound r X x & inc x X)).
Proof. 
rewrite /lower_bound/has_least/least=> or Xr.
rewrite (proj2 (iorder_osr or Xr)); split.
  move=> [a [aX h]]; exists a => //;split; first by apply:Xr.
  move=> y yX; move: (h _ yX); apply:iorder_gle1.
move=> [x [xsr hyp] xX]; ex_tac. 
by move=> y yX; apply/iorder_gle0P => //; apply: hyp.
Qed.

Lemma greatest_elementP X r: order r -> sub X (substrate r) ->
  (has_greatest (induced_order r X) <->
   (exists2 x, upper_bound r X x & inc x X)).
Proof.
rewrite /upper_bound/has_greatest/greatest=> or Xr. 
rewrite (proj2 (iorder_osr or Xr)); split.
  move=> [a []]; aw=> aX h; exists a => //;split; first by apply:Xr.
  move=> y yX; move: (h _ yX); apply:iorder_gle1.
move=> [x [xsr hyp] xX]; ex_tac.
by move=> y yX; apply/iorder_gle0P => //; apply: hyp.
Qed.

(** A set can be bounded above, below, or both *)

Definition bounded_above r X := exists x, upper_bound r X x.
Definition bounded_below r X := exists x, lower_bound r X x.
Definition bounded_both r X := bounded_above r X /\ bounded_below r X.

Lemma bounded_above_sub X Y r:
  sub Y X -> bounded_above r X  -> bounded_above r Y.
Proof. move=> YX [x ux]; exists x; apply: (sub_upper_bound ux YX). Qed.

Lemma bounded_below_sub X Y r:
  sub Y X -> bounded_below r X  -> bounded_below r Y.
Proof. move=>  YX [x ux]; exists x; apply: (sub_lower_bound ux YX). Qed.

Lemma bounded_both_sub X Y r:
  sub Y X -> bounded_both r X  -> bounded_both r Y.
Proof. 
move => YX [p1 p2].
split; [ apply: (bounded_above_sub YX p1) | apply: (bounded_below_sub YX p2)].
Qed.

Lemma singleton_bounded  x r:
  singletonp x -> order r -> sub x (substrate r) -> bounded_both r x.
Proof. 
move=> [y yp] or xsr.
have ysr: inc y (substrate r) by apply: xsr;rewrite yp; fprops.
have yy: gle r y y by order_tac. 
by split; exists y; split=>//; rewrite yp; move=> z /set1_P=> ->.
Qed.

(** ** Least upper bound and greatest lower bound *)

Definition greatest_induced r X x := greatest (induced_order r X) x.
Definition least_induced r X x := least (induced_order r X) x.

Definition greatest_lower_bound r X x :=
  greatest_induced r (Zo (substrate r) (lower_bound r X)) x.
Definition least_upper_bound r X x :=
  least_induced r (Zo (substrate r) (upper_bound r X)) x.
  
Lemma glbP r X:
  order r -> sub X (substrate r) ->  forall x,
  (greatest_lower_bound r X x <-> (lower_bound r X x
    /\ forall z, lower_bound r X z -> gle r z x)).
Proof. 
rewrite /greatest_lower_bound/greatest_induced/greatest=> or Xr x.
set T:= Zo _ _.
have sT: sub T (substrate r) by apply: Zo_S.
rewrite (proj2 (iorder_osr or sT)).
have tp z : inc z T <-> lower_bound r X z.
  by split; [ case/Zo_P | move => lb;apply:Zo_i => //; case:lb].
split.
  move=> [/tp ha hyp]; split => // z lbz.
  move/tp: lbz => /hyp;apply: iorder_gle1.
move=> [lbx hyp]; move/tp: (lbx) => xT.
by split => // y yT; apply /iorder_gle0P=> //; apply:hyp; apply/tp.
Qed.

Lemma lubP r X:
  order r -> sub X (substrate r) ->  forall x,
  (least_upper_bound r X x <-> (upper_bound r X x
    /\ forall z, upper_bound r X z -> gle r x z)).
Proof.
rewrite /least_upper_bound/least_induced/least=>or Xr x.
set T:= Zo _ _.
have sT: sub T (substrate r) by apply: Zo_S.
rewrite (proj2 (iorder_osr or sT)).
have tp z : inc z T <-> upper_bound r X z.
  by split; [ case/Zo_P | move => lb;apply:Zo_i => //; case:lb].
split.
  move=> [/tp ha hyp]; split => // z lbz.
  move/tp: lbz => /hyp;apply: iorder_gle1.
move=> [lbx hyp]; move/tp: (lbx) => xT.
by split => // y yT; apply /iorder_gle0P=> //; apply:hyp; apply/tp.
Qed.

Lemma supremum_unique X r: order r -> uniqueness (least_upper_bound r X). 
Proof. 
rewrite /least_upper_bound => or.
exact:(unique_least (proj1 (iorder_osr or (Zo_S (p:=upper_bound r X))))).
Qed.

Lemma infimum_unique X r: order r -> uniqueness (greatest_lower_bound r X). 
Proof. 
rewrite /greatest_lower_bound => or.
exact: (unique_greatest (proj1 (iorder_osr or (Zo_S (p:=lower_bound r X))))). 
Qed.

(** Definition of the supremum or infimum of a set or a pair *)


Definition infimum r X :=
  the_greatest (induced_order r (Zo (substrate r) (lower_bound r X))).
Definition supremum r X :=
  the_least (induced_order r (Zo (substrate r) (upper_bound r X))).
Definition sup r x y := supremum r (doubleton x y).
Definition inf r x y := infimum r (doubleton x y).
Definition has_supremum r X := (exists x, least_upper_bound r X x).
Definition has_infimum r X := (exists x, greatest_lower_bound r X x).

Lemma supremum_pr1 X r:
  order r -> has_supremum r X ->
  least_upper_bound r X (supremum r X).
Proof.
move => or [z h].
apply: the_least_pr => //; last by exists z.
exact: (proj1 (iorder_osr or (Zo_S(p:=upper_bound r X)))).
Qed.

Lemma infimum_pr1  X r:
  order r -> has_infimum r X ->
  greatest_lower_bound r X (infimum r X).
Proof.
move => or [z h].
apply: the_greatest_pr => //; last by exists z.
exact: (proj1 (iorder_osr or (Zo_S(p:=lower_bound r X)))).
Qed.

Hint Resolve supremum_pr1 infimum_pr1: fprops.


Lemma supremum_pr2 r X a: order  r -> 
  least_upper_bound r X a -> a = supremum r X.
Proof. 
move=> or le.
have hs: has_supremum r X by exists a. 
exact: (supremum_unique or le (supremum_pr1 or hs)).
Qed.

Lemma infimum_pr2 r X a: order r ->
  greatest_lower_bound r X a -> a = infimum r X.
Proof. 
move=> or le.
have hs: has_infimum r X by  exists a. 
exact: (infimum_unique or le (infimum_pr1 or hs)).
Qed.

Lemma inc_supremum_substrate X r:
  order r -> sub X (substrate r) -> has_supremum r X ->
  inc (supremum r X) (substrate r).
Proof. 
move=> or Xsr hs.
by move: (supremum_pr1 or hs)=> /(lubP or Xsr) [[aa _] _].
Qed.

Lemma inc_infimum_substrate  X r:
  order r -> sub X (substrate r) -> has_infimum r X ->
  inc (infimum r X) (substrate r).
Proof.
move=> or Xsr hs.
by move: (infimum_pr1 or hs)=> /(glbP or Xsr) [[aa _] _].
Qed.

Lemma supremum_pr X r: 
  order r ->  sub X (substrate r) -> has_supremum r X ->
  (upper_bound r X (supremum r X) /\ 
    forall z, upper_bound r X z -> gle r (supremum r X) z).
Proof. by move=> or Xsr /(supremum_pr1 or) /(lubP or Xsr). Qed.
  
Lemma infimum_pr X r: 
  order r ->  sub X (substrate r) -> has_infimum r X ->
  (lower_bound r X (infimum r X) /\ 
    forall z, lower_bound r X z -> gle r z (infimum r X)).
Proof. by move=> or Xsr /(infimum_pr1 or) /(glbP or Xsr). Qed.

(** Properties of sup and inf of pairs *)

Lemma sup_pr a b r:
  order r -> inc a (substrate r) -> inc b (substrate r) ->
  has_supremum r (doubleton a b) -> 
  [/\ gle r a (sup r a b),  gle r b (sup r a b) &
    forall z, gle r a z ->  gle r b z -> gle r (sup r a b) z].
Proof.
move=> or ast bsr hs.
have sd: sub (doubleton a b) (substrate r) by apply: sub_set2.
move: (supremum_pr or sd hs) => [[sr h1] h2]; split; try apply: h1; fprops.
move=> z az bz; apply: h2.
split; [by order_tac | by  move=>y; case /set2_P => ->].
Qed.

Lemma inf_pr a b r: 
  order r -> inc a (substrate r) -> inc b (substrate r) ->
  has_infimum r (doubleton a b) -> 
  [/\ gle r (inf r a b) a,  gle r (inf r a b) b &
    forall z, gle r z a -> gle r z b -> gle r z (inf r a b)].
Proof.
move=> or ast bsr hs.
have sd: sub (doubleton a b) (substrate r) by apply: sub_set2.
move: (infimum_pr or sd hs)  => [[sr h1] h2]; split; try apply: h1; fprops.
move=> z az bz; apply: h2.
split; [by order_tac | by  move=>y; case /set2_P => ->].
Qed.

Lemma lub_set2 r x y z:
  order r -> gle r x z -> gle r y z ->
  (forall t, gle r x t -> gle r y t -> gle r z t) ->
  least_upper_bound r (doubleton x y) z.
Proof. 
move=> or xz yz h.
move:(arg1_sr xz)(arg1_sr yz) => xsr ysr.
apply/(lubP or); first by move=>t /set2_P;case => ->. 
split; first by split; [order_tac | by move=>t /set2_P;case => ->].
move=> t [_ tb]; apply: h; apply: tb; fprops.
Qed.

Lemma glb_set2 r x y z:
  order r -> gle r z x  -> gle r z y ->
  (forall t, gle r t x -> gle r t y -> gle r t z) ->
  greatest_lower_bound r (doubleton x y) z.
Proof.
move=> or xz yz h.
move:(arg2_sr xz) (arg2_sr yz) => xsr ysr. 
apply/(glbP or); first by move=>t /set2_P;case => ->. 
split;first by split; [order_tac | by move=>t /set2_P;case => ->].
move=> t [_ tb]; apply: h; apply: tb; fprops.
Qed.

(** Link between supremum and greatest element *)

Lemma greatest_is_sup r X a:
  order r -> sub X (substrate r) ->
  greatest_induced r X a -> least_upper_bound r X a.
Proof. 
move=> or Xsr []; rewrite (proj2 (iorder_osr or Xsr)) => aX h.
apply/(lubP or Xsr); split.
  split; [by apply: Xsr | move=> y yX; move: (h _ yX); apply:iorder_gle1 ].
by move=> z [zs h2]; apply: (h2 _ aX).
Qed.

Lemma least_is_inf  r X a:
  order r -> sub X (substrate r) ->
  least_induced r X a -> greatest_lower_bound r X a.
Proof. 
move=> or Xsr []; rewrite (proj2 (iorder_osr or Xsr)) => aX h.
apply/(glbP or Xsr); split.
  split; [by apply: Xsr | by move=> y yX; move: (h _ yX); apply:iorder_gle1].
by move=> z [zs h2]; apply: (h2 _ aX).
Qed.

Lemma inf_sup_oppP r X:
  order r -> sub X (substrate r) -> forall a,
  (greatest_lower_bound r X a <-> least_upper_bound (opp_order r) X a).
Proof. 
move=> or Xsr a.
have [oor osr] := (opp_osr or).
have Xsor: sub X (substrate (opp_order r)) by ue.
apply:(iff_trans (glbP or Xsr a)); symmetry; apply:(iff_trans(lubP oor Xsor a)).
by split; move => [pa pb]; split;
    try (apply /(opposite_lower_boundP or) => //);
  move => z /(opposite_lower_boundP or) => h; apply/igraph_pP; apply: pb.
Qed.

Lemma sup_inf_oppP r X:
  order r -> sub X (substrate r) -> forall a,
  (least_upper_bound r X a <-> greatest_lower_bound (opp_order r) X a).
Proof.
move=> or Xsr a; symmetry.
have [oor osr] := (opp_osr or).
have Xsor: sub X (substrate (opp_order r)) by ue.
move: (inf_sup_oppP oor Xsor a).
by rewrite /opp_order (igraph_involutive (proj41 or)).
Qed.

Lemma sup_inf_opp r X:
  order r -> sub X (substrate r) -> has_supremum r X ->
  (has_infimum (opp_order r) X /\ infimum (opp_order r) X = supremum r X).
Proof.
move => or sa sb.
have hh:= (proj1 (opp_osr or)).
move: (supremum_pr1 or sb) => sc.
move /(sup_inf_oppP or sa): sc => w.
by split; [ exists (supremum r X) | symmetry; apply: infimum_pr2].
Qed.

Lemma inf_sup_opp r X:
  order r -> sub X (substrate r) -> has_infimum r X ->
  (has_supremum (opp_order r) X /\ supremum (opp_order r) X = infimum r X).
Proof.
move => or sa sb.
have hh:= (proj1 (opp_osr or)).
move: (infimum_pr1 or sb) => sc.
move /(inf_sup_oppP or sa): sc => w.
by split; [ exists (infimum r X) | symmetry; apply: supremum_pr2].
Qed.

(** Supremum and infimum of the empty set *)

Lemma set_of_lower_bounds_set0 r:
  Zo (substrate r) (lower_bound r emptyset) = substrate r.
Proof. 
apply: extensionality; first by apply: Zo_S. 
move=> x xsr; apply /Zo_P; split=>//; split=>// y;case; case.
Qed.

Lemma set_of_upper_bounds_set0 r:
  Zo (substrate r) (upper_bound r emptyset) = substrate r.
Proof.
apply: extensionality; first by apply: Zo_S. 
move=> x xsr; apply /Zo_P; split=>//; split=>// y;case; case.
Qed.

Lemma lub_set0 r: order r -> forall x,
  (least_upper_bound r emptyset x = least r x). 
Proof. 
move=> or; rewrite /least_upper_bound set_of_upper_bounds_set0. 
by rewrite /least_induced iorder_substrate.
Qed.


Lemma glb_set0 r: order r ->  forall x,
  greatest_lower_bound r emptyset x = greatest r x. 
Proof.
move=> or; rewrite /greatest_lower_bound set_of_lower_bounds_set0. 
by rewrite /greatest_induced iorder_substrate. 
Qed.

(** Supremum and infimum for inclusion order *)

Lemma setI_inf s E: sub s (\Po E) ->
  greatest_lower_bound (subp_order E) s 
  (Yo (nonempty s) (intersection s) E).
Proof.
move=> sp.
have [oi si1] := (subp_osr E).
have nee: ~ nonempty emptyset by move/nonemptyP.
case: (emptyset_dichot s)=> h. 
  by rewrite h Y_false // glb_set0 //; apply: wholeset_greatest.
Ytac0.  
have si: sub (intersection s) E by apply:setI_sub2 => i/sp /setP_P.
have ss: sub s (substrate (subp_order E)) by rewrite si1.
apply/(glbP oi ss); rewrite /lower_bound si1; split.
  split; first by apply/setP_P.
  move=> y ys; apply /subp_gleP; split => //.
    by apply/setP_P; apply: sp.
  by apply: setI_s1.
move=> z [] /setP_P zE hyp.
apply /subp_gleP; split => // t tz. 
by apply: (setI_i h) => y /hyp /subp_gleP [_ _]; apply.
Qed.

Lemma setU_sup s E: sub s (\Po E) ->
  least_upper_bound (subp_order E) s (union s). 
Proof.
move=> sp.
have [oi si1] := (subp_osr E).
have su:sub (union s) E by apply: setU_s2; move=> y /sp /setP_P.
have aux: sub s (substrate (subp_order E)) by ue.
apply/(lubP oi aux); rewrite /upper_bound si1; split.
  split; first by apply/setP_P.
  move => y ys.
  have sy: sub y (union s) by apply: setU_s1.
  by apply/subp_gleP; split => //; move: (sp _ ys) => /setP_P.
move=> z [zE hyp]; apply/subp_gleP; split => //; first by apply/setP_P.
by apply: setU_s2 => y /hyp /subp_gleP [_ _]. 
Qed.

Lemma setU_sup1 s F E: sub F (\Po E) ->
  sub s F -> inc (union s) F ->
  least_upper_bound (sub_order F) s (union s). 
Proof. 
move=> Fp sF uF.
have [oi si1] := (sub_osr F).
have sss: sub s (substrate (sub_order F)) by ue.
apply/(lubP oi sss); rewrite /upper_bound si1; split.
  by split => // y ys; apply /sub_gleP; split => //; fprops;apply: setU_s1.
move=> z [zF hyp]; apply /sub_gleP; split => //.
by apply: setU_s2=> y /hyp /sub_gleP [_ _].
Qed.

Lemma setI_inf1 s F E (T := (Yo (nonempty s) (intersection s) E)):
  sub F (\Po E) ->
  sub s F -> inc T F ->
  greatest_lower_bound (sub_order F) s T.
Proof.
rewrite /T;move=> Fp sF ssF.
have [oi si1] := (sub_osr F).
have sss: sub s (substrate (sub_order F)) by ue.
apply/(glbP oi sss); rewrite /lower_bound si1; split.
  split =>// y ys; apply /sub_gleP; split; fprops.
  have nes: (nonempty s) by exists y.
  Ytac0;apply: setI_s1=>//.
move=>z [zF hyp]; apply /sub_gleP; split => //.
case: (emptyset_dichot s) => sp.
  by rewrite  Y_false;[apply /setP_P /Fp | rewrite sp; move /nonemptyP ].
Ytac0;move=> t tz; apply: setI_i=>//. 
by move=> y /hyp  /sub_gleP [_ _]; apply.
Qed.

(** Supremum for extension order: is least common extension *)

Lemma sup_extension_order1 E F T f:
  sub T (sub_functions E F) ->
  least_upper_bound (opp_order (extension_order E F)) T f ->
  forall u v x, inc u T -> inc v T ->  inc x (source u) ->  inc x (source v) -> 
    Vf u x = Vf v x.
Proof.
move=> Ts lef.
have [oe sr] := (extension_osr E F).
have [oo so] := (opp_osr oe).
have sTe: sub T (substrate (extension_order E F)) by ue.
have sT:sub T (substrate (opp_order (extension_order E F))) by ue.
move: lef => /(lubP oo sT) [[fs ub] hyp] u v x uT vT xs ys.
by rewrite (extension_order_pr (ub _ uT) xs) (extension_order_pr (ub _ vT) ys).
Qed.


Lemma sup_extension_order2  E F T:
  sub T (sub_functions E F) ->
  (forall u v x, inc u T -> inc v T -> inc x (source u) -> inc x (source v) -> 
    Vf u x = Vf v x) ->
  exists x, [/\ least_upper_bound (opp_order (extension_order E F)) T x,
     (source x = unionb (Lg T source)),
     (Imf x = unionb (Lg T (fun u => (Imf u)))) &
     (graph x) = unionb (Lg T graph)].
Proof.
move=> Ts ag.
set h := Lg T source.  
have fp: forall i, inc i (domain h) -> function_prop i (Vg h i) F.
  rewrite /h/function_prop; aw => i iT; rewrite LgV //.
  move: (Ts _ iT) => /sfunctionsP. 
  by move => [pa pb pc].
have ag1: forall i j, inc i (domain h) -> inc j (domain h) -> 
    agrees_on ((Vg h i) \cap (Vg h j)) i j. 
  rewrite /h; aw;move=> i j iT jT; rewrite ! LgV//.
  split; [ by apply: subsetI2l |  by apply: subsetI2r | ].
  move=> a /setI2_P [ai aj]; by apply: ag.
move:(extension_covering fp ag1).
set g := (common_ext h id F); move => [[fg sf tg] gg rg vg].
have [oe sr] := (extension_osr E F).
have [oo os] := (opp_osr oe).
have ssEF: sub_functions E F = 
    substrate (opp_order (extension_order E F)) by ue.
have Tso: sub T (substrate (opp_order (extension_order E F))) by aw; ue. 
have sTe: sub T (substrate (extension_order E F)) by ue.
have xss:inc g (sub_functions E F).
  apply /sfunctionsP;split => //.
  rewrite sf /h; move=> t /setUb_P; aw; move => [y yT]; rewrite LgV// => ty.
  by move /sfunctionsP: (Ts _ yT) =>  [_ yE _]; apply: yE.
exists g; rewrite rg gg /h; aw; split => //; apply /(lubP oo Tso); split. 
  hnf;rewrite - ssEF; split => //. 
  move=> y yT; move:(Ts _ yT) => yss.  
  apply/extension_order_P2; split => //.
  move => t ta; rewrite gg /h; apply /setUb_P; aw; ex_tac;rewrite LgV //.
move=> z; rewrite /upper_bound - ssEF; move => [zss hyp].
apply /extension_order_P2; split => //.
move=> t; rewrite gg /h;move /setUb_P; aw; move => [y yT];rewrite LgV// => tgg.
by move: (hyp _ yT) => /extension_order_P2 [_ _]; apply.
Qed.

(** Supremum and infimum of the range of a function *)

Definition sup_funp r f := least_upper_bound r (Imf f).
Definition inf_funp r f:= greatest_lower_bound r (Imf f).

Lemma sup_funP r f: order r -> substrate r = target f ->
  function f -> forall x,
  (sup_funp r f x <-> [/\ inc x (target f),
    (forall a, inc a (source f) -> gle r (Vf f a) x)
    &forall z, inc z (target f) -> (forall a, inc a (source f) 
      -> gle r (Vf f a) z) -> gle r x z]).
Proof. 
move=> or sr ff x.
have si: sub (Imf f) (substrate r).  
   by rewrite sr; apply: fun_image_Starget1.
have gf: sgraph (graph f) by fprops. 
apply: (iff_trans (lubP or si x)); split.
  move=> [[xt p1] p2];split => //; first by ue.
  move=> a afs; apply: p1; first by apply/(Imf_P ff);ex_tac.
  move=> z zt sh; apply: p2; split; first by ue.
  by move=> y /(Imf_P ff)  [u usf ->]; apply: sh.
move=> [xt p1 p2];split.
  split; first by ue.
  by move=> yy/(Imf_P ff) [u usf ->]; apply: p1.
move=> z [ztg p3]; apply: p2; first by ue.
move=> a asf; apply: p3; apply /(Imf_P ff); ex_tac.
Qed.

Lemma inf_funP r f: order r -> substrate r = target f ->
  function f -> forall x,
  (inf_funp r f x <->
   [/\ inc x (target f), 
     (forall a, inc a (source f) -> gle r x (Vf f a))
    & forall z, inc z (target f) -> (forall a, inc a (source f) 
     -> gle r z (Vf f a)) -> gle r z x]).
Proof. 
move=> or sr ff x.
have si: sub (Imf f) (substrate r).
  by rewrite sr; apply: fun_image_Starget1.
have gf: sgraph (graph f) by fprops. 
apply: (iff_trans (glbP or si x)); split.
  move=> [[xt p1] p2]; split => //; first by ue.
  move=> a afs; apply: p1; first by apply/(Imf_P ff);ex_tac.
  move=> z zt sh; apply: p2; split; first by ue.
  by move=> y /(Imf_P ff)  [u usf ->]; apply: sh.
move=> [xt p1 p2];split.
  split; first by ue.
  by move=> yy/(Imf_P ff) [u usf ->]; apply: p1.
move=> z [ztg p3]; apply: p2; first by ue.
move=> a asf; apply: p3; apply /(Imf_P ff); ex_tac.
Qed.

(** Supremum and infimum of the range of a functional graph *)

Definition sup_graphp r f := least_upper_bound r (range f).
Definition inf_graphp r f := greatest_lower_bound r (range f).
Definition has_sup_graph r f := has_supremum r (range f).
Definition has_inf_graph r f := has_infimum r (range f).
Definition sup_graph r f:= supremum r (range f).
Definition inf_graph r f := infimum r (range f).

Lemma sup_graph_pr1 r f: 
  order r -> sub (range f) (substrate r) -> has_sup_graph r f ->
  least_upper_bound r (range f) (sup_graph r f).
Proof. 
rewrite /has_sup_graph/sup_graph/sup_graphp=> or sr hs; fprops. 
Qed.

Lemma inf_graph_pr1 r f:
  order r -> sub (range f) (substrate r) -> has_inf_graph r f ->
  greatest_lower_bound r (range f) (inf_graph r f).
Proof. rewrite /has_inf_graph/inf_graph/inf_graphp; fprops. Qed.

Lemma sup_graphP r f: order r -> sub (range f) (substrate r) ->
  fgraph f -> forall x,
  (sup_graphp r f x <-> [/\ inc x (substrate r),
   (forall a, inc a (domain f) -> gle r (Vg f a) x)
   & forall z, inc z (substrate r) -> (forall a, inc a (domain f) 
     -> gle r (Vg f a) z) -> gle r x z]).
Proof. 
move=> or sr fg.
have gf: sgraph f by fprops.
split.
  move/(lubP or sr) => [[pa pb] pc]; split => //. 
     by move=> a ad; apply: pb;fprops.
  move=> z zs p; apply: pc; split => //.
  move=> y /(rangeP gf) [t Jg].
  by move: (pr2_V fg Jg); aw; move=> ->; apply: p; ex_tac.  
move=> [xs p1 p2]; apply /(lubP or sr); split.
  split=>//; move=> y  /(rangeP gf) [z Jg]; move: (pr2_V fg Jg); aw.  
  move=> ->; apply: p1; aw; ex_tac.
move=> z [zr p3]; apply: p2 =>//; move=> a ad; apply: p3; fprops.
Qed.

Lemma inf_graphP r f: order r -> sub (range f) (substrate r) ->
  fgraph f -> forall x,
  (inf_graphp r f x <->  [/\ inc x (substrate r),
   (forall a, inc a (domain f) -> gle r x (Vg f a))
   & forall z, inc z (substrate r) -> (forall a, inc a (domain f) 
     -> gle r z (Vg f a)) -> gle r z x]).
Proof.
move=> or sr fg.
have gf: sgraph f by fprops.
split.
  move/(glbP or sr) => [[pa pb] pc]; split => //. 
    by move=> a ad; apply: pb;fprops.
  move=> z zs p; apply: pc; split => //.
  move=> y /(rangeP gf) [t Jg].
  by move: (pr2_V fg Jg); aw;  move=> ->; apply: p; ex_tac.  
move=> [xs p1 p2]; apply /(glbP or sr); split.
  split=>//; move=> y /(rangeP gf) [z Jg]; move: (pr2_V fg Jg); aw.  
  move=> ->; apply: p1; aw; ex_tac.
move=> z [zr p3]; apply: p2 =>//; move=> a ad; apply: p3; fprops.
Qed.

Theorem compare_inf_sup1 r A: order r -> sub A (substrate r) ->
  has_supremum r A -> has_infimum r A ->
  A = emptyset ->
  (greatest r (infimum r A) /\  least r (supremum r A)).
Proof.
move=> or As /(supremum_pr1 or) hs /(infimum_pr1 or) hi Ae.
move: hs hi; rewrite Ae glb_set0 // lub_set0 //. 
Qed.

Theorem compare_inf_sup2 r A: order r -> sub A (substrate r) ->
  has_supremum r A -> has_infimum r A ->
  nonempty A -> gle r (infimum r A) (supremum r A).
Proof. 
move=> or As hs hi [x xA].
move /(lubP or As): (supremum_pr1 or hs) => [[uE p1] _ ].
move /(glbP or As): (infimum_pr1 or hi) => [[vE p2] _].
move: (p1 _ xA)(p2 _ xA)=> q1 q2; order_tac.
Qed.

Theorem sup_increasing r A B: order r -> sub A (substrate r) ->
  sub B (substrate r) -> sub A B ->
  has_supremum r A -> has_supremum r B->
  gle r (supremum r A) (supremum r B).
Proof.
move=> or As Bs AB sA sB.
move /(lubP or As): (supremum_pr1 or sA) => [_ p1].
move /(lubP or Bs): (supremum_pr1 or sB) => [[uB p2] _].
by apply: p1; split => // t tA; apply:p2; apply: AB.
Qed.

Theorem inf_decreasing r A B: order r -> sub A (substrate r) ->
  sub B (substrate r) -> sub A B ->
  has_infimum r A -> has_infimum r B ->
  gle r (infimum r B) (infimum r A) .
Proof.
move=> or As Bs AB sA sB.
move /(glbP or As): (infimum_pr1 or sA) => [_ p1].
move /(glbP or Bs): (infimum_pr1 or sB) => [[uB p2] _].
by apply: p1; split => // t tA; apply:p2; apply: AB.
Qed.


Lemma sup_increasing_gen r
   (W := Zo (\Po (substrate r)) (fun z => has_supremum r z)):
   order r ->
   increasing_fun (Lf (supremum r) W (substrate r))  (sub_order W) r.
Proof.
move => or.
move:(sub_osr W) => [qa qb].
have ax :lf_axiom (supremum r) W (substrate r).
  by move => t /Zo_P[/setP_P ra rb]; apply: inc_supremum_substrate. 
split => //; first  by hnf; aw; split => //; apply: lf_function. 
move => a b /sub_gleP [aX bX lab]; rewrite !LfV //.
move: aX bX => /Zo_P [/setP_P ra rb] /Zo_P [/setP_P rc rd].
by apply:sup_increasing.
Qed.

 
Lemma inf_decreasing_gen r
   (W := Zo (\Po (substrate r)) (fun z => has_infimum r z)):
   order r ->
   decreasing_fun (Lf (infimum r) W (substrate r))  (sub_order W) r.
Proof.
  move => or.
move:(sub_osr W) => [qa qb].
have ax :lf_axiom (infimum r) W (substrate r). 
  by move => t /Zo_P[/setP_P ra rb]; apply: inc_infimum_substrate. 
split => //; first  by hnf; aw; split => //; apply: lf_function. 
move => a b /sub_gleP [aX bX lab]; rewrite !LfV//.
move: aX bX => /Zo_P [/setP_P ra rb] /Zo_P [/setP_P rc rd].
by apply:inf_decreasing.
Qed.

Lemma sup_increasing1 r f j:
  order r -> fgraph f -> sub (range f) (substrate r) -> sub j (domain f) ->
  has_sup_graph r f  ->  
  has_sup_graph r (restr f j) ->
  gle r (sup_graph r (restr f j)) (sup_graph r f).
Proof. 
move => or fg sr sj hs1 hs2.
have srr: sub (range (restr f j)) (range f) by apply: restr_range1.
apply: sup_increasing=>//; apply: sub_trans srr sr.
Qed.

Lemma inf_decreasing1 r f j: 
  order r -> fgraph f -> sub (range f) (substrate r) -> sub j (domain f) ->
  has_inf_graph r f ->  has_inf_graph r (restr f j) ->
  gle r (inf_graph r f) (inf_graph r (restr f j)) .
Proof.
move => or fg sr sj hs1 hs2.
have srr: sub (range (restr f j)) (range f) by apply: restr_range1.
apply: inf_decreasing=>//; apply: sub_trans srr sr.
Qed.

Lemma sup_increasing2 r f f': 
  order r -> fgraph f ->  fgraph f' ->  domain f = domain f' ->
  sub (range f) (substrate r) -> sub (range f') (substrate r) ->
  has_sup_graph r f  ->  has_sup_graph r f'->
  (forall x , inc x (domain f) -> gle r (Vg f x) (Vg f' x)) ->
  gle r (sup_graph r f) (sup_graph r f').
Proof.
move=> or gf gf' df sr sr' hs hs' ale.
move /(sup_graphP or sr gf): (sup_graph_pr1 or sr hs) =>[sgr p1 p2].
move /(sup_graphP or sr' gf'): (sup_graph_pr1 or sr' hs') =>[sgr' p1' p2']. 
apply: p2=>// a ad.
apply: (@order_transitivity r _ (Vg f' a) _ or); [apply:ale=>//|apply: p1']; ue.
Qed.

Lemma inf_increasing2 r f f': 
  order r -> fgraph f ->  fgraph f' ->  domain f = domain f' ->
  sub (range f) (substrate r) -> sub (range f') (substrate r) ->
  has_inf_graph r f ->  
  has_inf_graph r f'->
  (forall x , inc x (domain f) -> gle r (Vg f x) (Vg f' x)) ->
  gle r (inf_graph r f) (inf_graph r f').
Proof. 
move=> or gf gf' df sr sr' hs hs' ale.
move /(inf_graphP or sr gf): (inf_graph_pr1 or sr hs) =>[sgr p1 p2].
move /(inf_graphP or sr' gf'): (inf_graph_pr1 or sr' hs') =>[sgr' p1' p2']. 
apply: p2'=>// a ad.
apply: (@order_transitivity r _ (Vg f a) _ or);[apply: p1 |apply: ale=>//]; ue.
Qed.


Lemma sup_increasing2_gen r X
  (W := Zo (gfunctions X (substrate r)) (has_sup_graph r)) :
  order r -> 
  increasing_fun (Lf (sup_graph r) W (substrate r)) 
   (induced_order (order_graph X (substrate r) r) W) r.
Proof.
move => or.
move: (order_graph_osr X (erefl (substrate r)) or).
rewrite /W; set r' := order_graph _ _ _; set G := gfunctions _ _.
set W1 := Zo _ _; move => [qa qb].
have s1: sub W1 (substrate r') by rewrite  qb; apply: Zo_S.
move: (iorder_osr qa s1) => [qv qd].
have ax: lf_axiom (sup_graph r) W1 (substrate r).
  move => t /Zo_P [/gfunctions_P2 [ma mb mc] ha]. 
  move: (proj1 (sup_graph_pr1 or mc ha)); rewrite iorder_sr //.
    by move/Zo_S.
  apply: Zo_S.
split => //; first by hnf; aw; split => //; apply: lf_function.
move => a b /iorder_gleP [aW1 aw1 la]; rewrite !LfV//.
move: aW1 => /Zo_P [/gfunctions_P2 [ma mb mc] ha]. 
move: aw1 => /Zo_P [/gfunctions_P2 [ma' mb' mc'] ha']. 
have sd: domain a = domain b by ue.
apply:sup_increasing2 => //; rewrite mb.
by move/graph_on_P1: la => /proj33. 
Qed.
  

Lemma inf_increasing2_gen r X
  (W := Zo (gfunctions X (substrate r)) (has_inf_graph r)) :
  order r -> 
  increasing_fun (Lf (inf_graph r) W (substrate r)) 
   (induced_order (order_graph X (substrate r) r) W) r.
Proof.
move => or.
move: (order_graph_osr X (erefl (substrate r)) or).
rewrite /W; set r' := order_graph _ _ _; set G := gfunctions _ _.
set W1 := Zo _ _; move => [qa qb].
have s1: sub W1 (substrate r') by rewrite  qb; apply: Zo_S.
move: (iorder_osr qa s1) => [qv qd].
have ax: lf_axiom (inf_graph r) W1 (substrate r).
  move => t /Zo_P [/gfunctions_P2 [ma mb mc] ha]. 
  move: (proj1 (inf_graph_pr1 or mc ha)); rewrite iorder_sr //.
    by move/Zo_S.
  apply: Zo_S.
split => //; first by hnf; aw; split => //; apply: lf_function.
move => a b /iorder_gleP [aW1 aw1 la]; rewrite !LfV //.
move: aW1 => /Zo_P [/gfunctions_P2 [ma mb mc] ha]. 
move: aw1 => /Zo_P [/gfunctions_P2 [ma' mb' mc'] ha']. 
have sd: domain a = domain b by ue. 
apply:inf_increasing2 => //; rewrite mb.
by move/graph_on_P1: la => /proj33. 
Qed.

(** Associativity of sup and inf *)

Section supAssoc.
Variables r f c: Set.
Hypothesis (or:order r) (fgf: fgraph f) 
   (rf: sub (range f) (substrate r)) (df: domain f = unionb c).

Lemma sup_A x:
  (forall l, inc l (domain c) -> has_sup_graph r (restr f (Vg c l))) ->
  (sup_graphp r f x <->
    sup_graphp r (Lg (domain c) (fun l => sup_graph r (restr f (Vg c l)))) x).
Proof. 
move=> alsup. 
set g:= Lg _  _.
have fgg:fgraph g by rewrite /g; fprops.
have ranr: forall a, inc a (domain c) -> 
   (sub (range (restr f (Vg c a))) (substrate r)).
  move => a ac; apply: sub_trans rf; apply: restr_range1 => //.
  rewrite df => s su; union_tac.
have srh: (sub (range g) (substrate r)). 
  move=> t /(Lg_range_P)  [b bd st].
  move: (sup_graph_pr1 or (ranr b bd) (alsup _ bd)).
  by rewrite st; move /(lubP or (ranr b bd)) => [[? _] _].
split.
  move/(sup_graphP or rf fgf) =>[xsr p1 p2].
  apply/(sup_graphP or srh fgg); split => //.
    rewrite /g; aw;move=> a adc; rewrite !LgV //.
    move: (sup_graph_pr1 or (ranr a adc) (alsup _ adc)). 
    move /(lubP or (ranr a adc))=> [_ ]; apply.
    split=> // y /funI_P [z /funI_P [s sv ->] ->]; aw; apply: p1.
    rewrite df; union_tac.
  move=> z zr hyp.
  apply: p2 =>// a; rewrite df => /setUb_P [y yd aV].
  apply: (@order_transitivity  r _ (sup_graph r (restr f (Vg c y))) _ or).
    move: (sup_graph_pr1 or (ranr y yd) (alsup _ yd)). 
    move/(lubP or (ranr y yd)) => [[ _ p] _]; apply: p. 
    apply /funI_P; exists (J a (Vg f a)); aw; trivial;apply /funI_P; ex_tac.
  move: hyp; rewrite /g; aw => xx; move: (xx _ yd); rewrite LgV//.
move/(sup_graphP or srh fgg) =>[xsr p1 p2].
have dgdc: domain g =  domain c by rewrite /g; aw.
rewrite dgdc in p1 p2.
apply/(sup_graphP or rf fgf); split => //.
  move=> a; rewrite df => /setUb_P [y yd aV].
  move: (p1 _ yd) => aux.
  apply: (order_transitivity or) aux. 
  move: (sup_graph_pr1 or (ranr y yd) (alsup _ yd)).
  move /(lubP or (ranr y yd)) => [[_ p] _]; rewrite /g LgV//; apply:p.
  apply /funI_P; exists (J a (Vg f a)); aw; trivial; apply /funI_P;ex_tac.
move=> z zr h; apply: p2 =>//.
move=> a ad;rewrite /g LgV //.
move: (sup_graph_pr1 or (ranr a ad) (alsup _ ad)). 
move /(lubP or (ranr a ad)) => [_ p]; apply:p.
split=>// y /funI_P [t /funI_P [s sa ->] ->]; aw; apply: h.
rewrite df; union_tac.
Qed.

(* copy of the proof for the sup *)
Lemma inf_A x:
  (forall l, inc l (domain c) -> has_inf_graph r (restr f (Vg c l))) ->
  (inf_graphp r f x <->
   inf_graphp r (Lg (domain c) (fun l => inf_graph r (restr f (Vg c l)))) x).
Proof. 
move=> alinf.
set g:= Lg _  _.
have fgg:fgraph g by rewrite /g; fprops.
have ranr: forall a, inc a (domain c) -> 
   (sub (range (restr f (Vg c a))) (substrate r)).
  move => a ac; apply: sub_trans rf; apply: restr_range1 => //.
  rewrite df => s su; union_tac.
have srh: (sub (range g) (substrate r)). 
  move=> t /(Lg_range_P)  [b bd st].
  move: (inf_graph_pr1 or (ranr b bd) (alinf _ bd)).
  by rewrite st; move /(glbP or (ranr b bd)) => [[? _] _].
split.
  move/(inf_graphP or rf fgf) =>[xsr p1 p2].
  apply/(inf_graphP or srh fgg); split => //.
    rewrite /g; aw;move=> a adc; rewrite LgV//.
    move: (inf_graph_pr1 or (ranr a adc) (alinf _ adc)). 
    move /(glbP or (ranr a adc))=> [_ ]; apply.
    split=> // y /funI_P [z /funI_P [s sv ->] ->]; aw; apply: p1.
    rewrite df; union_tac.
  move=> z zr hyp.
  apply: p2 =>//; move=> a; rewrite df => /setUb_P [y yd aV].
  apply: (@order_transitivity  r _ (inf_graph r (restr f (Vg c y))) _ or).
    by move: hyp; rewrite /g; aw => xx; move: (xx _ yd); rewrite LgV.
  move: (inf_graph_pr1 or (ranr y yd) (alinf _ yd)). 
  move/(glbP or (ranr y yd)) => [[ _ p] _]. apply: p.
  apply /funI_P; exists (J a (Vg f a)); aw;trivial; apply /funI_P; ex_tac.
move/(inf_graphP or srh fgg) =>[xsr p1 p2].
have dgdc: domain g =  domain c by rewrite /g; aw.
rewrite dgdc in p1 p2.
apply/(inf_graphP or rf fgf); split => //.
  move=> a; rewrite df => /setUb_P [y yd aV].
  move: (p1 _ yd) => aux.
  apply: (order_transitivity or aux). 
  move: (inf_graph_pr1 or (ranr y yd) (alinf _ yd)).
  move /(glbP or (ranr y yd)) => [[_ p] _]; rewrite LgV //; apply:p.
  apply /funI_P; exists (J a (Vg f a)); aw;trivial;apply /funI_P;ex_tac.
move=> z zr h; apply: p2 =>//.
move=> a ad;rewrite LgV //.
move: (inf_graph_pr1 or (ranr a ad) (alinf _ ad)). 
move /(glbP or (ranr a ad)) => [_ p]; apply:p.
split=>// y /funI_P [t /funI_P [s sa ->] ->]; aw; apply: h.
rewrite df; union_tac.
Qed.

Lemma sup_A1:
  (forall l, inc l (domain c) -> has_sup_graph r (restr f (Vg c l))) ->
  (has_sup_graph r f <->
  has_sup_graph r (Lg (domain c) (fun l => sup_graph r (restr f (Vg c l))))).
Proof. 
move=> alsup.
by split; move=> [x xs]; move: (sup_A x alsup) => aux; exists x; apply/ aux.
Qed.

Lemma inf_A1:
  (forall l, inc l (domain c) -> has_inf_graph r (restr f (Vg c l))) ->
  (has_inf_graph r f <->
   has_inf_graph r (Lg (domain c) (fun l => inf_graph r (restr f (Vg c l))))).
Proof.
move=> alsup.
by split; move=> [x xs]; move: (inf_A x alsup) => aux; exists x; apply/aux.
Qed.

Theorem sup_A2:
  (forall l, inc l (domain c) -> has_sup_graph r (restr f (Vg c l))) ->
  ((has_sup_graph r f <-> 
    has_sup_graph r (Lg (domain c)(fun l => sup_graph r (restr f (Vg c l))))) /\
  (has_sup_graph r f -> sup_graph r f = 
    sup_graph r (Lg (domain c) (fun l => sup_graph r (restr f (Vg c l)))))).
Proof. 
move=> alsup.
split; first by apply: sup_A1=>//. 
move=> hyp; rewrite /sup_graph.
set (g:= Lg (domain c) (fun l  => sup_graph r (restr f (Vg c l)))).    
have lu:= (sup_graph_pr1 or rf hyp).
rewrite -(supremum_unique or lu (supremum_pr1 or hyp)). 
move/(sup_A (sup_graph r f) alsup): lu => lug.
have lug': least_upper_bound r (range g) (supremum r (range g)).
  by apply: supremum_pr1 => //; exists (sup_graph r f).
by rewrite -(supremum_unique or lug lug'). 
Qed.

Theorem inf_A2:
  (forall l, inc l (domain c) -> has_inf_graph r (restr f (Vg c l))) ->
  ((has_inf_graph r f <-> 
    has_inf_graph r (Lg (domain c)(fun l => inf_graph r (restr f (Vg c l))))) /\
  (has_inf_graph r f -> inf_graph r f = 
    inf_graph r (Lg (domain c) (fun l => inf_graph r (restr f (Vg c l)))))).
Proof. 
move=>  alsup.
split; first by apply: inf_A1=>//. 
move=> hyp; rewrite /inf_graph. 
set (g:= Lg (domain c) (fun l  => inf_graph r (restr f (Vg c l)))).    
move: (inf_graph_pr1 or rf hyp)=> lu. 
rewrite -(infimum_unique or lu (infimum_pr1 or hyp)). 
move /(inf_A (inf_graph r f) alsup): lu => lug.
have lug': greatest_lower_bound r (range g) (infimum r (range g)).
  by apply: infimum_pr1 => //; exists (inf_graph r f). 
by rewrite -(infimum_unique or lug lug'). 
Qed.

End supAssoc.

Lemma inf_A_alt r f c x:  (* proof via sup *)
  order r -> fgraph f ->  sub (range f) (substrate r) ->
  (domain f) = (unionb c) ->
  (forall l, inc l (domain c) -> has_inf_graph r (restr f (Vg c l))) ->
  (inf_graphp r f x <->
   inf_graphp r (Lg (domain c) (fun l => inf_graph r (restr f (Vg c l)))) x).
Proof. 
move => ha hb hc he hf.
move:(opp_osr ha) =>[or' sr'].
move: (hc);rewrite - sr' => hc'.
set r':= opp_order r.
have pa i: inc i (domain c) -> sub (range (restr f (Vg c i))) (substrate r).
  move => zc.
  have pb:sub (Vg c i) (domain f) by rewrite he => t ta; union_tac.
  by move: (sub_trans (restr_range1 hb pb) hc'); rewrite sr'.
have hf' i: inc i (domain c) -> has_sup_graph r' (restr f (Vg c i)).
  move => lc; move:(hf _ lc); rewrite /has_inf_graph /has_sup_graph => ww.
  exact (proj1 (inf_sup_opp ha (pa _ lc) ww)).
have pc: inf_graphp r f x <-> sup_graphp (opp_order r) f x
   by apply:inf_sup_oppP.
apply: (iff_trans pc); apply: (iff_trans (sup_A or' hb hc' he x hf')).
rewrite /sup_graphp /inf_graphp.
set a := Lg (domain c) _; set b := Lg (domain c) _.
have ->: a = b.
  apply: Lg_exten => i idc.
  exact: (proj2 (inf_sup_opp ha (pa _ idc) (hf _ idc))).
apply:iff_sym; apply:inf_sup_oppP => //.
rewrite /b /inf_graph Lg_range => t /funI_P [z za ->].
apply:(inc_infimum_substrate ha (pa _ za) (hf _ za)).
Qed.

Definition partial_fun f x m := restr f (x *s1 m).

Lemma sup_A3 r f x y:
  order r -> fgraph f ->  sub (range f) (substrate r) ->
  domain f = x \times y ->
  (forall m, inc m y -> has_sup_graph r (partial_fun f x m)) ->
  ((has_sup_graph r f <->
    has_sup_graph r (Lg y (fun m => sup_graph r  (partial_fun f x m)))) /\
  (has_sup_graph r f -> sup_graph r f = 
    sup_graph r (Lg y (fun m => sup_graph r (partial_fun f x m))))).
Proof. 
move=> or fgf sr df alsup.
set (c:= Lg y (fun m => x \times (singleton m))).
have co1: fgraph c by rewrite /c; fprops. 
have co2: domain f = unionb c. 
  rewrite /c df; set_extens t. 
    move => /setX_P [pt Px Qy]. apply/setUb_P1; ex_tac; apply: setX_i; fprops.
  move /setUb_P1 => [z zy /setX_P [pt Px /set1_P Qy]].
  apply: setX_i; fprops; ue.
have dc:  y = domain c by rewrite /c; aw.
have pfx: forall m, inc m y ->  partial_fun f x m = restr f (Vg c m).
  by move=> m my; rewrite LgV.
have hsg: forall l, inc l (domain c) -> has_sup_graph r (restr f (Vg c l)).
  by move=> l;  rewrite -dc=> ld; rewrite - pfx //;apply: alsup.
have <-: Lg (domain c) (fun l => sup_graph r (restr f (Vg c l))) =
    Lg y (fun m => sup_graph r (partial_fun f x m)).
  by rewrite -dc; apply: Lg_exten; move=> t ty /=; rewrite pfx. 
exact: sup_A2.
Qed.

Lemma inf_A3 r f x y:
  order r -> fgraph f ->  sub (range f) (substrate r) ->
  domain f = x \times y ->
  (forall m, inc m y -> has_inf_graph r (partial_fun f x m)) ->
  ((has_inf_graph r f <->
    has_inf_graph r (Lg y (fun m => inf_graph r  (partial_fun f x m)))) /\
  (has_inf_graph r f -> inf_graph r f = 
    inf_graph r (Lg y (fun m => inf_graph r (partial_fun f x m))))).
Proof. 
move=> or fgf sr df alinf.
set (c:= Lg y (fun m => x \times (singleton m))).
have co1: fgraph c by rewrite /c; fprops. 
have co2: (domain f) = (unionb c). 
  rewrite /c df; set_extens t. 
    move => /setX_P [pt Px Qy]. apply/setUb_P1; ex_tac; apply: setX_i; fprops.
  move /setUb_P1 => [z zy /setX_P [pt Px /set1_P Qy]].
  apply: setX_i; fprops; ue.
have dc: y = domain c by rewrite /c; aw.
have pfx: forall m, inc m y ->  partial_fun f x m = restr f (Vg c m).
  by move=> m my; rewrite LgV.
have hsg: forall l, inc l (domain c) -> has_inf_graph r (restr f (Vg c l)).
  by move=> l; rewrite -dc=> ld; rewrite - pfx //;apply: alinf.
have <-: Lg (domain c) (fun l => inf_graph r (restr f (Vg c l))) =
    Lg y (fun m : Set => inf_graph r (partial_fun f x m)). 
  by rewrite  -dc;  apply: Lg_exten; move=> t ty /=;  rewrite pfx.
exact: inf_A2.
Qed.

(** We compute the supremum of a product by taking the supremum of 
each component  *)

Lemma sup_in_product_aux g A (f := fam_of_substrates g)
  (Ai:= fun i => (Vfs (pr_i f i) A)):
  order_fam g -> sub A (productb f) ->
  forall i, inc i (domain g) -> sub (Ai i) (substrate (Vg g i)).
Proof.
move=> Ha Hb i id. 
have dfdg: domain f = domain g by rewrite /f /fam_of_substrates; aw.
have ->: substrate (Vg g i) = Vg f i by rewrite LgV.
have Hc: sub A (source (pr_i f i)) by rewrite /pr_i; aw.
have He: function (pr_i f i) by apply: pri_f => //; ue.
move=> t /(Vf_image_P He Hc) [u uA ->]. 
have ->: (Vg f i = target (pr_i f i)) by rewrite /pr_i; aw. 
Wtac.
Qed.

Theorem sup_in_product g A
  (f := fam_of_substrates g)
  (Ai:= fun i => (Vfs (pr_i f i) A))
  (has_sup := forall i, inc i (domain g) -> has_supremum (Vg g i) (Ai i)):
    order_fam g -> sub A (productb f) ->
    ((has_sup <-> has_supremum (order_product g) A) /\
      (has_sup -> supremum (order_product g) A = 
        Lg (domain g) (fun i => supremum (Vg g i) (Ai i)))).
Proof. 
move=> po Ab.
move: (po)=> allo.
have fgf: fgraph f by apply: fos_graph.
have df: domain f = domain g by rewrite /f; aw.
have als: forall i, inc i (domain g) -> substrate (Vg g i) = Vg f i.
  by move=> i idg; rewrite  LgV.
have Asi: forall i, inc i (domain g) -> sub A (source (pr_i f i)).
   by move=> i idg; rewrite /pr_i; aw.
have afi: forall i, inc i (domain g) -> function (pr_i f i).
  move => i idg; apply: pri_f =>//; ue.
have Ais:=(sup_in_product_aux po Ab). 
have p1: (has_sup -> (forall i, inc i (domain g) -> 
    least_upper_bound (Vg g i) (Ai i) (supremum (Vg g i) (Ai i)))). 
  move => hts i idg; apply: (supremum_pr1 (allo _ idg)); apply: hts =>//.
set mysup := Lg _ _.
have [opg srg] := order_product_osr allo.
have hlu: has_sup -> least_upper_bound (order_product g) A mysup.
  move=> hst.
  have mp: inc mysup (productb f).
    rewrite /mysup; apply/ setXb_P;split => //; [fprops | by aw |].
    rewrite df; move=> i idg; rewrite LgV //.
    by rewrite -als //; apply: inc_supremum_substrate; fprops; apply:Ais.
  have sas :sub A (substrate (order_product g)) by ue. 
  apply/(lubP opg  sas);split.
    split; first by rewrite srg.  
    move=> y yA; apply/order_product_gleP => //.
    split => //; first by apply: Ab. 
    move=> i idg; rewrite LgV //.
    move: (supremum_pr (allo _ idg) (Ais _ idg) (hst _ idg)). 
    move=> [[_ h]_]; apply: h.
    apply  /(Vf_image_P (afi _ idg) (Asi _ idg)).
    by ex_tac; rewrite -df in idg; rewrite  (pri_V idg (Ab _ yA)).
  move=> z [zs zp]; apply /order_product_gleP => //.
  split=>//; first by rewrite  srg in  zs.
  move=> i idg.
  move: (supremum_pr (allo _ idg) (Ais _ idg) (hst _ idg)). 
  rewrite LgV//; move=> [_]; apply. 
  split; first by apply:prod_of_substrates_p => //; move: zs; ue.
  have As:= (Asi _ idg).
  move=> y; move /(Vf_image_P (afi _ idg) (Asi _ idg)) => [u uA ->].
  rewrite -df in idg; rewrite  (pri_V idg (Ab _ uA)).
  move: (zp _ uA) => /(order_product_gleP)  [_ _]; apply; ue.
have hsu: has_sup -> has_supremum (order_product g) A.
  by move=> hst;  exists mysup; apply: hlu.
have g2: has_sup-> supremum (order_product g) A = mysup.
  move => hst; move:(hlu hst) => s1; move:(supremum_pr1 opg (hsu hst)) => s2.
  by apply: (supremum_unique opg s2 s1).
split=>//;split =>//.
have sAs: sub A (substrate (order_product g)) by ue.
move=> [x] /(lubP opg sAs) [[xs ub] lub].
move=> i idg.
move: (allo _ idg) => p2; move: (Ais _ idg)=> p3; move: (Asi _ idg)=> p4.
have fi: function (pr_i f i) by apply: pri_f=>//; ue.
exists (Vg x i); apply/(lubP p2 p3).
move: xs; rewrite srg; move/(prod_of_substratesP) => [fgx dx iVs].
split.
  split; first by apply: iVs.
  move=> y /(Vf_image_P (afi _ idg) (Asi _ idg)) [u uA ->].
  rewrite -df in idg; rewrite  (pri_V idg (Ab _ uA)).
  move: (ub  _ uA) => /(order_product_gleP)  [_ _]; apply; ue.
move=> z [zs h4].
set (y:= Lg (domain g) (fun j=> Yo(j = i) z (Vg x j))). 
have ->: (z = Vg y i) by rewrite LgV //; Ytac0. 
have yp: inc y (productb f).
  apply/setXb_P; rewrite /y df;split => //; aw; fprops.
  move=> k kd; rewrite LgV// -als//;Ytac ki; first by rewrite ki; apply: zs.
  by apply: iVs.
have aux: (upper_bound (order_product g) A y). 
  split;first by rewrite srg.
  move=> t tA; apply/(order_product_gleP); split => //; first by apply: Ab.
  move => k kd; rewrite LgV//.
  move: (ub  _ tA) => /(order_product_gleP) [_ _ h5].
  Ytac ki; last by apply: h5. 
  rewrite ki; apply: h4; apply/(Vf_image_P (afi _ idg) (Asi _ idg)); ex_tac.
  by rewrite -df in idg; rewrite  (pri_V idg (Ab _ tA)).
by move: (lub _ aux) => /(order_product_gleP) [_ _ ]; apply.
Qed.

Theorem inf_in_product g A
  (f := fam_of_substrates g)
  (Ai:= fun i => (Vfs (pr_i f i) A))
  (has_inf := forall i, inc i (domain g) -> has_infimum (Vg g i) (Ai i)):
    order_fam g -> sub A (productb f) ->
    ((has_inf <-> has_infimum (order_product g) A) /\
      (has_inf -> infimum (order_product g) A = 
        Lg (domain g) (fun i => infimum (Vg g i) (Ai i)))).
Proof.
move => ofg sA.
move: (order_product_opp_osr ofg).
set g' := fam_of_opp g.
set f' := fam_of_substrates g'.
move => [[Ha Hb] Hc].
have hb: domain g = domain g' by rewrite /g' /fam_of_opp; aw.
have ha: allf g sgraph by move => i /ofg [].
move: (fam_of_opp_sr ha); rewrite -/f -/g' -/f' => ff'.
have hc: order_fam g' by apply:fam_of_opp_or.
have hd:sub A (productb f') by rewrite - ff'.
have Hd: forall i, inc i (domain g) -> order (Vg g i) by [].
have He:=(sup_in_product_aux ofg sA).
set hi':= forall i, inc i (domain g') ->
     has_supremum (Vg g' i) (Vfs (pr_i f' i) A).
have ra: has_inf <-> hi'.
  rewrite /has_inf /hi' /g' -ff' /fam_of_opp; aw; split => H i idg.
    have pa: order (Vg g i) by apply: Hd.
    have pb: has_infimum (Vg g i) (Ai i) by apply:H.
    rewrite LgV//. 
    by move:(H _ idg) => [w ww]; exists w; apply /inf_sup_oppP => //; apply:He.
  have pa: order (Vg g i) by apply: Hd.
  have pb: sub (Ai i) (substrate (Vg g i)) by apply: He.
  move: (H _ idg) => [w ww]; exists w; apply/inf_sup_oppP => //; move: ww; aw.
rewrite LgV//. 
have Hf: (prod_of_substrates g') = (prod_of_substrates g).
   by rewrite /prod_of_substrates -/f -/f' ff'.
have [opg spg]:= (order_product_osr ofg).
have Hg: sub A (substrate (order_product g')) by rewrite Hb.
have Hg': sub A (substrate (order_product g)) by ue.
have rb:has_infimum (order_product g) A <-> has_supremum (order_product g') A.
  split; move =>[x xinf]; exists x; rewrite ? Hc; apply/inf_sup_oppP => //; ue.
move:(sup_in_product hc hd); rewrite -/hi'; move => [sa sb].
have sa': has_inf <-> has_infimum (order_product g) A.
  by apply:(iff_trans ra); apply: (iff_trans sa); apply: iff_sym.
split => // hiT; move/sa':(hiT) => hif.
move/ra:(hiT) => hiT'; move: (sb hiT').
move: (proj2(inf_sup_opp opg Hg' hif)).
rewrite -Hc -hb => -> ->; apply:Lg_exten => i idg. 
rewrite -/f' -ff'  LgV//. 
exact: (proj2(inf_sup_opp (Hd _ idg) (He _ idg) (hiT _ idg))).
Qed.

Theorem inf_in_product_alt g A (* copy of sup_in_product *)
  (f := fam_of_substrates g)
  (Ai:= fun i => (Vfs (pr_i f i) A))
  (has_inf := forall i, inc i (domain g) -> has_infimum (Vg g i) (Ai i)):
    order_fam g -> sub A (productb f) ->
    ((has_inf <-> has_infimum (order_product g) A) /\
      (has_inf -> infimum (order_product g) A = 
        Lg (domain g) (fun i => infimum (Vg g i) (Ai i)))).
Proof.
move=> po Ab.
have fgf: fgraph f by apply: fos_graph.
have df: domain f = domain g by rewrite /f; aw.
have als: forall i, inc i (domain g) -> substrate (Vg g i) = Vg f i.
  by move=> i id; rewrite LgV.
have Asi: forall i, inc i (domain g) -> sub A (source (pr_i f i)).
  by move=> i idg; rewrite /pr_i; aw.
have afi: forall i, inc i (domain g) -> function (pr_i f i).
  move => i idg; apply: pri_f =>//; ue.
have Ais:=(sup_in_product_aux po Ab). 
have p1: (has_inf -> (forall i, inc i (domain g) -> 
    greatest_lower_bound (Vg g i) (Ai i) (infimum (Vg g i) (Ai i)))). 
  move => hts i idg;  apply: (infimum_pr1 (po _ idg)); apply: hts =>//.
set mysup := Lg _ _.
move:(order_product_osr po) => [opg srg].
have hlu: has_inf -> greatest_lower_bound (order_product g) A mysup.
  move=> hst.
  have mp: inc mysup (productb f).
    rewrite /mysup; apply/setXb_P;split => //; [fprops | by aw |].
    rewrite df; move=> i idg; rewrite LgV //.
    by rewrite -als //; apply: inc_infimum_substrate; fprops; apply: Ais.
  have sas :sub A (substrate (order_product g)) by ue.
  apply/(glbP opg  sas);split.
    split; first  by ue.
    move=> y yA; apply/order_product_gleP => //.
    split  => //;first by apply: Ab. 
    move=> i idg; rewrite LgV //.
    move: (infimum_pr (po _ idg) (Ais _ idg) (hst _ idg)). 
    move=> [[_ h]_]; apply: h.
    apply  /(Vf_image_P (afi _ idg) (Asi _ idg)).
    by ex_tac;  rewrite -df in idg; rewrite  (pri_V idg (Ab _ yA)).
  move=> z [zs zp]; apply /order_product_gleP => //.
  split => //; first by rewrite srg in  zs.
  move=> i idg.
  move: (infimum_pr (po _ idg) (Ais _ idg) (hst _ idg)). 
  rewrite LgV//; move=> [_]; apply. 
  split; first by apply:prod_of_substrates_p => //; move: zs; ue.
  move: (Asi _ idg) => As.
  move=> y; move /(Vf_image_P (afi _ idg) (Asi _ idg)) => [u uA ->].
  rewrite -df in idg; rewrite  (pri_V idg (Ab _ uA)).
  move: (zp _ uA) => /(order_product_gleP)  [_ _]; apply; ue.
have hsu: has_inf -> has_infimum (order_product g) A.
  by move=> hst;  exists mysup; apply: hlu.
have g2: has_inf-> infimum (order_product g) A = mysup.
  move => hst; move:(hlu hst) => s1; move:(infimum_pr1 opg (hsu hst)) => s2.
  by apply: (infimum_unique opg s2 s1).
split=>//;split =>//.
have sAs: sub A (substrate (order_product g)) by ue.
move=> [x] /(glbP opg sAs) [[xs ub] lub].
move=> i idg.
move: (po _ idg) => p2; move: (Ais _ idg)=> p3; move: (Asi _ idg)=> p4.
have fi: function (pr_i f i) by apply: pri_f=>//; ue.
exists (Vg x i); apply/(glbP p2 p3).
move: xs; rewrite srg; move/(prod_of_substratesP) => [fgx dx iVs].
split.
  split; first by apply: iVs.
  move=> y /(Vf_image_P (afi _ idg) (Asi _ idg)) [u uA ->].
  rewrite -df in idg; rewrite  (pri_V idg (Ab _ uA)).
  move: (ub  _ uA) => /(order_product_gleP)  [_ _ ]; apply; ue.
move=> z [zs h4].
set (y:= Lg (domain g) (fun j=> Yo(j = i) z (Vg x j))). 
have ->: (z = Vg y i) by rewrite LgV//; Ytac0. 
have yp: inc y (productb f).
  apply/setXb_P; rewrite /y df;split; aw; fprops.
  move=> k kd; rewrite LgV// -als//;Ytac ki; first by rewrite ki; apply: zs.
  by apply: iVs.
have aux: (lower_bound (order_product g) A y). 
  split;first by ue.
  move=> t tA; apply/(order_product_gleP); split => //; first by apply: Ab.
  move => k kd; rewrite LgV//.
  move: (ub  _ tA) => /(order_product_gleP) [_ _ h5].
  Ytac ki; last by apply: h5. 
  rewrite ki; apply: h4; apply/(Vf_image_P (afi _ idg) (Asi _ idg)); ex_tac.
  by rewrite -df in idg; rewrite  (pri_V idg (Ab _ tA)).
by move: (lub _ aux) => /(order_product_gleP) [_ _ ]; apply.
Qed.

(** Sup and inf of induced order *)

Theorem sup_induced1 r A F: order r -> sub F (substrate r) -> sub A F ->
  has_supremum r A -> has_supremum (induced_order r F) A ->
  gle r (supremum r A) (supremum (induced_order r F) A).
Proof.
move=> or Fs AF sA siA.
have [oi si]:= (iorder_osr or Fs).
have As:sub A (substrate r) by apply: sub_trans Fs. 
have Asi: sub A (substrate (induced_order r F)) by ue.
move: (supremum_pr1 or sA) (supremum_pr1 oi siA).
set (u:= supremum r A). 
set (v:=supremum (induced_order r F) A).
move=> /(lubP or As) [ub lub] /(lubP oi Asi) [[us ubi] lubi]; apply: lub.
move: us; rewrite si=> vF.
split;[ by apply: Fs | move=> y yA; move: (ubi _ yA); apply:iorder_gle1].
Qed.

Theorem inf_induced1 r A F: order r -> sub F (substrate r) -> sub A F ->
  has_infimum r A -> has_infimum (induced_order r F) A ->
  gle r (infimum (induced_order r F) A) (infimum r A).
Proof.
move=> or Fs AF sA siA.
have [oi si]:= (iorder_osr or Fs).
have As:sub A (substrate r) by apply: sub_trans Fs. 
have Asi: sub A (substrate (induced_order r F)) by ue. 
move: (infimum_pr1 or sA) (infimum_pr1 oi siA).
set (u:= infimum r A). 
set (v:=infimum (induced_order r F) A).
move=> /(glbP or As) [ub lub] /(glbP oi Asi) [[us ubi] lubi]; apply: lub.
move: us; rewrite si => vF.
split;[ by apply: Fs | move=> y yA; move: (ubi _ yA); apply:iorder_gle1].
Qed.

Theorem sup_induced2 r A F: order r -> sub F (substrate r) -> sub A F ->
  has_supremum r A -> inc (supremum r A)  F ->
  (has_supremum (induced_order r F) A /\
    supremum r A = supremum (induced_order r F) A).
Proof. 
move=>  or Fs AF hsA sAF.
have [oi si]:= (iorder_osr or Fs).
have As: sub A (substrate r) by apply: sub_trans Fs. 
have Asi:sub A (substrate (induced_order r F)) by ue.
have lub:=(supremum_pr1 or hsA).
have lubi: least_upper_bound (induced_order r F) A (supremum r A).  
  move: lub => /(lubP or As)  [[us ub] lub]; apply/(lubP oi Asi).
  split.
    split; [by rewrite si | move=> y yA; apply/iorder_gle0P; fprops].
  move=> z []; rewrite si // => zF zub.
  apply/iorder_gle0P; fprops; apply: lub; split; first by apply: Fs.
  move=> y yA; move: (zub _ yA); apply:iorder_gle1.
have aux: has_supremum (induced_order r F) A by exists (supremum r A). 
split=>//;apply: (supremum_unique oi lubi (supremum_pr1 oi aux)).
Qed.

Theorem inf_induced2 r A F: order r -> sub F (substrate r) -> sub A F ->
  has_infimum r A -> inc (infimum r A)  F ->
  (has_infimum (induced_order r F) A /\
    infimum r A = infimum (induced_order r F) A).
Proof. 
move=>  or Fs AF hsA sAF.
have [oi si]:= (iorder_osr or Fs).
have As: sub A (substrate r) by apply: sub_trans Fs. 
have Asi:sub A (substrate (induced_order r F)) by ue.
have lub:=(infimum_pr1 or hsA).
have lubi: greatest_lower_bound (induced_order r F) A (infimum r A).  
  move: lub => /(glbP or As)  [[us ub] lub]; apply/(glbP oi Asi).
  split.
    split; [by rewrite si|  move=> y yA; apply/iorder_gle0P; fprops].
  move=> z []; rewrite si // => zF zub.
  apply/iorder_gle0P; fprops; apply: lub; split; first by apply: Fs.
  move=> y yA; move: (zub _ yA); apply:iorder_gle1.
have aux: has_infimum (induced_order r F) A by exists (infimum r A). 
split=>//;apply: (infimum_unique oi lubi (infimum_pr1 oi aux)).
Qed.

(** ** Directed sets *)
(** Each pair is bounded above or below *)


Definition right_directed_prop r :=
  forall x y, inc x (substrate r) -> inc y (substrate r) ->
              exists z, gle r x z /\ gle r y z.
  
Definition right_directed r :=
  order r /\ forall x y, inc x (substrate r) -> inc y (substrate r) ->
    bounded_above r (doubleton x y).
Definition left_directed r :=
  order r /\ forall x y, inc x (substrate r) -> inc y (substrate r) ->
    bounded_below r (doubleton x y).

Lemma right_directedP r:
  right_directed r <-> (order r /\ right_directed_prop r).
Proof. 
split; move=> [or h]; split=>//.
  move=> x y xs ys; move: (h _ _ xs ys) => [t [ts tb]];exists t; split; fprops.
move=> x y xs ys. move: (h _ _ xs ys) => [z [xz yz]].
have zs: inc z (substrate r) by order_tac.
by exists z; split =>//; move=> t td; case /set2_P: td=>->.
Qed.

Lemma left_directedP r:
  left_directed r <-> (order r /\ 
    forall x y, inc x (substrate r) -> inc y (substrate r) -> exists z,
        gle r z x /\ gle r z y).
Proof. 
split; move=> [or h]; split=>//.
  move=> x y xs ys; move: (h _ _ xs ys)=> [t [ts tb]]; exists t; split; fprops.
move=> x y xs ys; move: (h _ _ xs ys) => [z [xz yz]].
have zs: inc z (substrate r) by order_tac.
by exists z; split =>//; move=> t td; case /set2_P: td => ->.
Qed.

Lemma greatest_right_directed r: order r ->
  has_greatest r -> right_directed r.
Proof.
move=> or [a [asr ga]]; apply right_directedP.
by split =>//; move=> x y xr yr; exists a; split; apply:ga.
Qed.

Lemma least_left_directed r: order r ->
  has_least r -> left_directed r.
Proof. 
move=> or [a [asr ga]]; apply /left_directedP.
by split =>//; move=> x y xr yr; exists a; split; apply:ga.
Qed.

Lemma opposite_right_directedP r: sgraph r ->
  (right_directed r <-> left_directed (opp_order r)).
Proof.
move=> gr.
apply: (iff_trans (right_directedP r)); symmetry. 
apply: (iff_trans (left_directedP (opp_order r))).
split; move=> [or hyp].
  move: (opp_osr or) => [].
  rewrite /opp_order igraph_involutive// => odr sa.
  split=> // x y xs ys.
  move: hyp; rewrite - sa => hyp.
  move: (hyp _ _ xs ys) => [z [xz yz]]. 
  by exists z; split => //;apply/igraph_pP.
have [ooi oisr]:= (opp_osr or).
split=>//; rewrite oisr; move => x y xs ys.
move: (hyp _ _ xs ys)=> [z [ xz yz]].
by exists z;split => //; apply/igraph_pP.
Qed.

Lemma opposite_left_directedP r: sgraph r ->
  (left_directed r <-> right_directed (opp_order r)).
Proof. 
move=>g; symmetry.
have go: sgraph  (opp_order r) by fprops.
move:(opposite_right_directedP go).
by rewrite /opp_order (igraph_involutive g). 
Qed.

(** products of directed sets are directed *)

Lemma setX_right_directed g:
  order_fam g -> (allf g right_directed) ->
  right_directed (order_product g).
Proof. 
move=> pa alri; move: (order_product_osr pa) => [pb pc].
apply/right_directedP; split =>//.
move=> x y xs ys.
set (z:= Lg (domain g)(fun i => choose (fun w =>
  upper_bound (Vg g i) (doubleton (Vg x i) (Vg y i)) w))).
have alu: (forall i, inc i (domain g) ->
    upper_bound (Vg g i) (doubleton (Vg x i) (Vg y i)) (Vg z i)).
  move=> i idg; rewrite LgV//.
  move: xs ys; rewrite pc.
  move/(prod_of_substratesP) => [_ _ p1] /(prod_of_substratesP)[_ _ p2].
  move:(p1 _ idg)(p2 _ idg)=> p3 p4.
  move: (alri _ idg)=> [t h]; move: (h _ _ p3 p4)=> [b bii]. 
  by apply:choose_pr; exists b.
have zs:inc z (substrate (order_product g)).
   rewrite pc;apply/prod_of_substratesP.
   split; first by rewrite/z; fprops.
     by rewrite/z; aw.
   by move => i idg; move: (alu _  idg); move=> [us ub]; apply: us.
move: xs ys zs; rewrite pc => xs ys zs.
exists z; split => //;apply /(order_product_gleP);
  split => //i idg; move: (alu _ idg); move=> [_ h]; apply: h; fprops.
Qed.

Lemma setX_left_directed g:
  order_fam g -> (allf g left_directed)
  -> left_directed (order_product g).
Proof.
move=> pa alri; move: (order_product_osr pa) => [pb pc].
apply/left_directedP; split =>//.
move=> x y xs ys.
set (z:= Lg (domain g)(fun i => choose (fun w =>
  lower_bound (Vg g i) (doubleton (Vg x i) (Vg y i)) w))).
have alu: (forall i, inc i (domain g) ->
    lower_bound (Vg g i) (doubleton (Vg x i) (Vg y i)) (Vg z i)).
  move=> i idg; rewrite LgV//.
  move: xs ys; rewrite pc.
  move/(prod_of_substratesP) => [_ _ p1] /(prod_of_substratesP)[_ _ p2].
  move:(p1 _ idg)(p2 _ idg)=> p3 p4.
  move: (alri _ idg)=> [t h]; move: (h _ _ p3 p4)=> [b bii]. 
  by apply:choose_pr; exists b.
have zs:inc z (substrate (order_product g)).
   rewrite pc;apply/(prod_of_substratesP).
   split; first by rewrite/z; fprops.
     by rewrite/z; aw.
   by move => i idg; move: (alu _  idg); move=> [us ub]; apply: us.
move: xs ys zs; rewrite pc => xs ys zs.
exists z;split => //; apply /(order_product_gleP); 
  split => // i idg; move: (alu _ idg); move=> [_ h]; apply: h; fprops.
Qed.

(** cofinal sets of directed sets are directed *)

Lemma cofinal_right_directed r A: 
  right_directed r -> cofinal r A -> right_directed (induced_order r A).
Proof. 
move/right_directedP => [or rr] [As co]; apply /right_directedP.
have [pa pb] := (iorder_osr or As).
split; [ exact | hnf; rewrite pb].
move=> x y xA yA; move: (rr _ _ (As _ xA)(As _ yA)) => [z [xz yz]].
move:(co _ (arg2_sr xz))=> [t tA tz].
exists t; split; apply/iorder_gle0P => // ;order_tac. 
Qed.

Lemma coinitial_left_directed r A:
  left_directed r -> coinitial r A -> left_directed (induced_order r A).
Proof. 
move/left_directedP => [or rr] [As co]; apply /left_directedP.
have [pa pb] := (iorder_osr or As).
split; [ exact | rewrite pb].
move=> x y xA yA; move: (rr _ _ (As _ xA)(As _ yA))=> [z [xz yz]].
move:(co _ (arg1_sr xz))=> [t tA tz].
exists t; split;apply/iorder_gle0P => //;order_tac. 
Qed.

(** a maximal element in a right directed set is greatest. *)

Theorem right_directed_maximal r x:
  right_directed r -> maximal r x -> greatest r x.
Proof. 
move=> rr [xsr ma]; split=>// t ts.
move /right_directedP:rr => [or rr].
by move:(rr  _ _  xsr ts) => [z [xz tz]]; rewrite - (ma  _ xz).
Qed.

Theorem left_directed_minimal r x:
  left_directed r -> minimal r x -> least r x.
Proof. 
move=> rr [xsr ma]; split=>// t ts.
move/left_directedP: rr => [or rr].
by move:(rr  _ _  xsr ts) => [z [xz tz]];rewrite - (ma  _ xz).
Qed.

(** ** Lattices *)

(* Each doubleton has a sup and an inf *)

Definition lattice r :=  order  r /\ 
  forall x y, inc x (substrate r) -> inc y (substrate r) ->
    (has_supremum r (doubleton x y) /\ has_infimum r (doubleton x y)).

Lemma lattice_sup_pr r a b:
  lattice r -> inc a (substrate r) -> inc b (substrate r) ->
  [/\ gle r a (sup r a b), gle r b (sup r a b) &
    forall z, gle r a z ->  gle r b z -> gle r (sup r a b) z].
Proof. 
move=>  [or lr] asr bsr.
by move: (lr _ _ asr bsr)=> [p1 p2]; apply: sup_pr.  
Qed.

Lemma lattice_inf_pr r a b:
  lattice r -> inc a (substrate r) -> inc b (substrate r) ->
  [/\ gle r (inf r a b) a,  gle r (inf r a b) b &
    forall z, gle r z a ->  gle r z b -> gle r z (inf r a b)].
Proof.
move=> [or lr] asr bsr.
by move: (lr _ _ asr bsr)=> [p1 p2]; apply: inf_pr.  
Qed.

Lemma inf_inclusion A x y: sub x A -> sub y A  ->  
  greatest_lower_bound (subp_order A) (doubleton x y) (x \cap y).
Proof. 
move=> xA yA.
have sd: (sub (doubleton x y) (\Po A)) by apply: sub_set2; apply/setP_P.
move: (setI_inf sd);rewrite Y_true //; apply: set2_ne.
Qed.

Lemma sup_inclusion A x y: sub x A -> sub y A  ->  
  least_upper_bound (subp_order A) (doubleton x y) (x \cup y).
Proof. 
move=>  xA yA.
have sd: (sub (doubleton x y) (\Po A)) by apply: sub_set2; apply/setP_P.
apply: (setU_sup sd). 
Qed.

(** Examples *)

Lemma setP_lattice A: lattice (subp_order A).
Proof. 
have [pa pb]:= (subp_osr A).
split; [exact | rewrite pb].
move=> x y /setP_P xp /setP_P yp; split.
  by exists (x \cup y); apply: sup_inclusion.
by exists (x \cap y); apply: inf_inclusion.
Qed.

Lemma setP_lattice_pr A x y (r := subp_order A):
    inc x (\Po A) -> inc y (\Po A) ->
    (sup r x y = x \cup y /\ inf r x y = x \cap y).
Proof.
move => /setP_P xA /setP_P yA.
have or := (proj1 (setP_lattice A)).
move: (inf_inclusion xA yA) (sup_inclusion xA yA) => pa pb.
by rewrite (infimum_pr2 or pa) (supremum_pr2 or pb).
Qed.

Lemma setX_lattice g:
  order_fam g -> (allf g lattice) ->
  lattice (order_product g).
Proof. 
move=>po all.
have [pa pb]:= (order_product_osr po).
split; [exact | rewrite pb].
move=> x y xs ys.
have sd: sub (doubleton x y) (prod_of_substrates g). 
  by move=> t;case /set2_P => ->. 
set (f := fam_of_substrates g). 
have fgf: fgraph f by apply: fos_graph.
have df: domain f = domain g by rewrite /f; aw.
have pf: productb f =  prod_of_substrates g by [].
have aux: (forall i, inc i (domain g) ->  exists u, exists v,
    [/\ inc u (substrate (Vg g i)), inc v (substrate (Vg g i)) &
    (Vfs (pr_i f i) (doubleton x y) = doubleton u v)]). 
  move=> i idg; exists (Vg x i); exists (Vg y i). 
  move: (xs) (ys) => /(prod_of_substratesP) [fx dx iVx] 
                     /(prod_of_substratesP) [fy dy iVy].
  split; first by apply: iVx.
    by apply: iVy.
  have sds: sub (doubleton x y) (source (pr_i f i)).
    rewrite /pr_i lf_source. 
    by move=> t; case /set2_P  => ->.  
  have fi: function (pr_i f i) by apply: pri_f=>//; ue. 
  have Wx: (Vf (pr_i f i) x = (Vg x i)) by apply: pri_V=>//; ue. 
  have Vfy: (Vf (pr_i f i) y = (Vg y i)) by apply: pri_V=>//; ue. 
  set_extens z. 
    move/(Vf_image_P fi sds)=> [u ud ->]; case /set2_P: ud => ->; ue.
  case /set2_P => ->;apply /(Vf_image_P fi sds); [exists x |exists y]; fprops.
move:(sup_in_product po sd) => [h _]; rewrite -h.
move:(inf_in_product po sd) => [h' _]; rewrite -h'.
split. 
  move=> i idg; move: (aux _ idg) => [u [v [us vs ->]]].
  move: (all _ idg)=> [_ lt]; move: (lt _ _ us vs)=> [lt1 lt2].
  apply: lt1.
move=> i idg; move: (aux _ idg) => [u [v [us vs ->]]].
move: (all _ idg)=> [_ lt]; move: (lt _ _ us vs)=> [lt1 lt2].
apply: lt2.
Qed.

Lemma lattice_directed r:
  lattice r -> (right_directed r /\ left_directed r).
Proof. 
move=> [or lr]; split; split =>// x y xs ys; move: (lr _ _ xs ys)=> [p1 p2].
  have sd: sub (doubleton x y) (substrate r) by  apply: sub_set2.
  by move: p1=> [s] /(lubP or sd)[ub _]; exists s.
have sd: sub (doubleton x y) (substrate r) by  apply: sub_set2.
by move: p2=> [s] /(glbP or sd)[ub _] ; exists s.
Qed.

Lemma lattice_opposite r: lattice r -> lattice (opp_order r).
Proof. 
move=>  [or lr]; move: (opp_osr or) => [oor soi]; split => //.
rewrite soi; move=> x y xs ys.
have [[x1 p1] [x2 p2]] := (lr _ _ xs ys).
split. 
  by exists x2; apply /(inf_sup_oppP or) => //; apply: sub_set2.
by exists x1; apply /(sup_inf_oppP or) => //; apply: sub_set2.
Qed.

Section Gminmax. 
Variable p:property.
Variable r:relation.
Hypothesis orA: forall x y, r x y -> r y x -> x = y.
Hypothesis orR: forall a, p a -> r a a.
Hypothesis orT:forall b a c, r a b -> r b c -> r a c.
Hypothesis orTe: forall a b, p a -> p b -> r a b \/ r b a.

Definition Gmax x y:=  Yo (r x y) y x.
Definition Gmin x y:=  Yo (r x y) x y.

Lemma Gmax_S x y: p x -> p y -> p (Gmax x y). 
Proof.  by move => ox oy; rewrite /Gmax;Ytac w. Qed.
Lemma Gmin_S x y: p x -> p y -> p (Gmin x y). 
Proof. by move => ox oy; rewrite /Gmin;Ytac w. Qed.

Lemma Gmax_E x y E: inc x E -> inc y E -> inc (Gmax x y) E.
Proof.  by move => ox oy; rewrite /Gmax;Ytac w. Qed.
Lemma Gmin_E x y E: inc x E -> inc y E -> inc (Gmin x y) E.
Proof.  by move => ox oy; rewrite /Gmin;Ytac w. Qed.


Lemma Gmax_xy x y: r x y -> Gmax x y = y.
Proof. by move => h; rewrite /Gmax; Ytac0. Qed.

Lemma Gmax_yx x y: r y x -> Gmax x y = x.
Proof. move => h; rewrite /Gmax; Ytac h1; [ apply:orA h h1 | done]. Qed.
 
Lemma Gmin_xy x y: r x y -> Gmin x y = x.
Proof. by move => h; rewrite /Gmin; Ytac0. Qed.

Lemma Gmin_yx x y: r y x -> Gmin x y = y.
Proof. move => h; rewrite /Gmin; Ytac h1 ; [ apply:orA h1 h | done]. Qed.

Lemma GmaxC x y: p x -> p y -> Gmax x y = Gmax y x.
Proof.
move => ox oy. 
case: (orTe ox oy) => h; first  by rewrite Gmax_xy // Gmax_yx.
rewrite Gmax_yx // Gmax_xy //. 
Qed.

Lemma GminC x y: p x -> p y -> Gmin x y = Gmin y x.
Proof.
move => ox oy.
case: (orTe ox oy) => h; first  by rewrite Gmin_xy // Gmin_yx.
rewrite Gmin_yx // Gmin_xy //. 
Qed.

Lemma Gmax_p1 x y: p x -> p y ->  r x (Gmax x y) /\ r y (Gmax x y).
Proof.
move => ox oy.
case: (orTe ox oy) => h. 
  by rewrite (Gmax_xy h); split => //; apply: orR.
by rewrite (Gmax_yx h); split => //; apply: orR.
Qed.

Lemma Gmin_p1 x y: p x -> p y -> r (Gmin x y)  x /\ r (Gmin x y) y.
Proof.
move => ox oy.
case: (orTe ox oy) => h. 
  by rewrite (Gmin_xy h); split => //; apply: orR.
by rewrite (Gmin_yx h); split => //; apply: orR.
Qed.

Lemma Gmax_p0 x y z: r x z -> r y  z -> r (Gmax x y) z.
Proof. by move => ha hb; rewrite /Gmax; Ytac h. Qed.

Lemma Gmin_p0 x y z: r z x -> r z y -> r z (Gmin x y).
Proof. by move => ha hb; rewrite /Gmin; Ytac h. Qed.

Lemma GmaxA x y z: p x -> p y -> p z -> 
  Gmax x (Gmax y z) = Gmax (Gmax x y) z.
Proof.
move =>ox oy oz.
case: (orTe ox oy) => h1. 
  rewrite (Gmax_xy h1); apply:Gmax_xy. 
  exact: (orT h1 (proj1 (Gmax_p1 oy oz))).
rewrite (Gmax_yx h1); case: (orTe ox oz) => h2.
  by rewrite (Gmax_xy (orT h1 h2)).
by rewrite (Gmax_yx (Gmax_p0 h1 h2)) (Gmax_yx h2).
Qed.

Lemma GminA x y z: p x -> p y -> p z -> 
    Gmin x (Gmin y z) = Gmin (Gmin x y) z.
Proof.
move =>ox oy oz.
case: (orTe oy oz) => h1. 
  rewrite (Gmin_xy h1); symmetry;apply:Gmin_xy. 
  exact: (orT (proj2 (Gmin_p1 ox oy)) h1).
rewrite (Gmin_yx h1); case: (orTe ox oy) => h2.
   by rewrite (Gmin_xy h2).
rewrite (Gmin_yx h2) (Gmin_yx h1); apply:Gmin_yx; apply: orT h1 h2.
Qed.
 
Lemma Gminmax x y z: 
  p x -> p y -> p z ->
  Gmin x (Gmax y z) = Gmax (Gmin x y) (Gmin x z).
Proof.
move => ox; wlog: y z / r y z.
   move => H oy oz; case: (orTe oy oz) => h; first  by apply:H.
   by rewrite (GmaxC oy oz)  (H _ _ h oz oy) GmaxC //; apply:Gmin_S.
move => yz oy oz;rewrite (Gmax_xy yz).
symmetry; apply: Gmax_xy;case: (orTe ox oy) => h1.
  by rewrite (Gmin_xy h1) (Gmin_xy (orT h1 yz));apply: orR.
by rewrite (Gmin_yx h1); apply:Gmin_p0.
Qed.

Lemma Gmaxmin x y z: p x -> p y -> p z ->
  Gmax x (Gmin y z) = Gmin (Gmax x y) (Gmax x z).
Proof.
move => ox; wlog: y z / r y z.
   move => H oy oz; case: (orTe oy oz) => h; first  by apply:H.
   by rewrite (GminC oy oz)  (H _ _ h oz oy) GminC //; apply:Gmax_S.
move => yz oy oz;rewrite (Gmin_xy yz).
symmetry; apply: Gmin_xy;case: (orTe ox oy) => h1.
  by rewrite (Gmax_xy h1) (Gmax_xy (orT h1 yz)).
rewrite (Gmax_yx h1); exact: (proj1 (Gmax_p1 ox oz)).
Qed.

  
End Gminmax.



(** ** Totally ordered sets *)

Definition ocomparable r x y := gle r x y \/ gle r y x.

Definition total_order r := 
  order r /\ {inc  (substrate r) &, (forall x y, ocomparable r x y)}.

Lemma total_orderP r:
  total_order r <->
    [/\ r \cg r = r,
    r \cap (inverse_graph r) = diagonal (substrate r)& 
    r \cup (inverse_graph r) =  coarse (substrate r) ].
Proof. 
rewrite /total_order.
split. 
  move=> [or to]; move /orderP: (or) => [p1 p2].
  split => //; set_extens x => xu.
   case /setU2_P: xu.
     have gr: (sgraph r) by fprops.
     apply: (sub_graph_coarse_substrate gr). 
   have  [oor sor] := (opp_osr or).
   have gr: sgraph  (opp_order r) by fprops.
   by rewrite - sor; apply: (sub_graph_coarse_substrate gr). 
  move: xu => /setX_P [ px Ps Qs]; rewrite - px.
  by case:(to _ _ Ps Qs)=> xx;apply/setU2_P;[ by left | right; apply/igraph_pP].
move=> [cg i2 u2]. 
have or :order r by apply/orderP.
split=>// x y xs ys.
have Jc: inc (J x y)  (coarse (substrate r)) by apply/setXp_P; split.
move: Jc; rewrite -u2;case /setU2_P=> xx; [by left | right].
by apply/igraph_pP.
Qed.

Lemma total_order_pr1 r x y:
  total_order r ->  inc x (substrate r) -> inc y (substrate r) ->
    [\/ glt r x y, glt r y x | x = y ].
Proof. 
move=> [_ p] xs ys.
case: (equal_or_not x y); [by constructor 3 | move =>  xy].
rewrite /glt; case:(p _ _ xs ys); [constructor 1 | constructor 2]; fprops.
Qed.

Lemma total_order_pr2  r x y:
  total_order r ->  inc x (substrate r) -> inc y (substrate r) ->
    (glt r x y \/ gle r y x).
Proof. 
move=> tor xs ys. 
move: tor=> [_ p]; rewrite /glt; case: (p _ _ xs ys); last by right.
by case: (equal_or_not x y); [  move=> ->; right | left].
Qed.

Lemma total_order_sub  r x:
  total_order r ->  sub x (substrate r) -> total_order (induced_order r x).
Proof. 
move=> [or tor] xs; move: (iorder_osr or xs) => [pa pb].
split; [ by exact | rewrite pb /ocomparable;aw; move=> a b asr bsr].
by case:(tor _ _ (xs _ asr) (xs _ bsr)) =>h; [left | right]; apply/iorder_gleP.
Qed.

Lemma total_order_small  r:
  order r -> small_set (substrate r) ->  total_order r.
Proof. 
move=> or ss; split=>// x y xs ys; rewrite (ss _ _ xs ys).
by left; order_tac. 
Qed.

Lemma total_order_opposite r:
  total_order r -> total_order (opp_order r).
Proof.
move=> [or tor]; hnf; move: (opp_osr or) => [oo ->]; split => // x y xs ys.
by case: (tor _ _ xs ys)=> h; [right |left]; apply/igraph_pP.
Qed.

(** If x is smaller than y, the pair has a supremum and an infimum *)

Lemma sup_comparable r x y: gle r x y ->
  order r -> least_upper_bound r (doubleton x y) y.
Proof. move=> xy or; apply: lub_set2 =>//;order_tac; order_tac. Qed.

Lemma inf_comparable r x y: gle r x y ->
  order r -> greatest_lower_bound r (doubleton x y) x.
Proof. move=> xy or; apply: glb_set2 =>//;order_tac; order_tac. Qed.

Lemma inf_comparable1 r x y: order r -> gle r x y ->
  inf r x y = x.
Proof. by symmetry; apply: infimum_pr2 =>//; apply: inf_comparable. Qed.

Lemma sup_comparable1 r x y: order r -> gle r x y ->
  sup r x y = y.
Proof. by symmetry; apply: supremum_pr2 =>//; apply :sup_comparable. Qed.

Lemma infimum_singleton r x:
   order r -> inc x (substrate r) -> infimum r (singleton x) = x.
Proof. by move=> or xsr;apply: inf_comparable1 => //; order_tac. Qed. 

Lemma supremum_singleton r x:
   order r -> inc x (substrate r) -> supremum r (singleton x) = x.
Proof. by move=> or xsr; apply: sup_comparable1=> //; order_tac. Qed. 

Lemma total_order_lattice r:
  total_order r -> lattice r.
Proof.
move=> [or tor]; split=>//.
move=> x y xsr ysr; case: (tor _ _ xsr ysr).
  move => hyp; split.
    by exists y; apply: sup_comparable. 
  by exists x; apply: inf_comparable.
rewrite set2_C => hyp; split.
  by exists x; apply: sup_comparable. 
by exists y; apply: inf_comparable.
Qed.


Lemma total_order_counterexample (r := (subp_order C2)):
  lattice r /\ ~ (total_order r). 
Proof. 
split; [ apply:setP_lattice | move=> [or]].
rewrite (proj2 (subp_osr C2)) => to. 
have sa: (inc (singleton C0) (\Po C2)). 
  apply/setP_P; move=> t /set1_P ->; fprops.
have sb: (inc (singleton C1) (\Po C2)).
  apply/setP_P; move=> t /set1_P ->; fprops.
case: (to _ _ sa sb) => /subp_gleP [_ _] /sub1setP /set1_P; fprops.
Qed.

Lemma total_order_directed r:
  total_order r -> (right_directed r /\ left_directed r).
Proof. by move=>to;  apply: lattice_directed; apply: total_order_lattice.  Qed.

Lemma inf_C r x y: inf r x y = inf r y x.
Proof. by rewrite /inf set2_C. Qed.

Lemma sup_C r x y: sup r x y = sup r y x.
Proof. by rewrite /sup set2_C. Qed.

Lemma least_greatest_pr r (E := substrate r): order r ->
 [/\ (has_least r -> 
         forall a, inc a E -> sup r (the_least r) a = a),
    (has_greatest r -> 
      forall a, inc a E -> inf r a (the_greatest r) = a),
    (has_least r ->
      forall a, inc a E -> inf r (the_least r) a = (the_least r))&
    (has_greatest r -> 
      forall a, inc a E -> sup r a (the_greatest r) = (the_greatest r))].
Proof. 
move=> or; split.
+ move => h a asr; apply: sup_comparable1 => //.
  by move: (the_least_pr or h)  => [_ sp]; apply: sp.
+ move => h a asr; apply: inf_comparable1 => //.
  by move: (the_greatest_pr or h)  => [_ sp]; apply: sp.
+ move => h a asr; apply: inf_comparable1 => //.
  by move: (the_least_pr or h)  => [_ sp]; apply: sp.
+ move => h a asr; apply: sup_comparable1 => //.
  by move: (the_greatest_pr or h)  => [_ sp]; apply: sp.
Qed.


Section LatticeProps.

Variable (r: Set).
Hypothesis lr: lattice r.
Let E := substrate r.

Lemma lattice_props: 
    ( (forall x y, inc x E->  inc y E -> inc (sup r x y) E)
      /\ (forall x y, inc x E->  inc y E -> inc (inf r x y) E)
      /\ (forall x y, inc x E->  inc y E -> sup r (inf r x y) y = y)
      /\ (forall x y, inc x E->  inc y E -> inf r (sup r x y) y = y)
      /\ (forall x y z, inc x E->  inc y E -> inc z E ->
        sup r x (sup r y z) = sup r (sup r x y) z)
      /\ (forall x y z, inc x E->  inc y E -> inc z E ->
        inf r x (inf r y z) = inf r (inf r x y) z)
      /\ (forall x, inc x E -> sup r x x = x) 
      /\ (forall x, inc x E -> inf r x x = x)
      /\ (forall x y, inc x E->  inc y E -> sup r (sup r x y) x = sup r x y)
      /\ (forall x y, inc x E->  inc y E -> inf r (inf r x y) x = inf r x y)
).
Proof.
move: (lr) => [or _].
have sa:(forall x y z, inc x E->  inc y E -> inc z E ->
        sup r x (sup r y z) = sup r (sup r x y) z).
  move => x y z xE yE zE.
  have [le1 le2 le3] := (lattice_sup_pr lr xE yE). 
  have [le4 le5 le6] := (lattice_sup_pr lr yE zE).
  have s1r: (inc  (sup r y z) (substrate r)) by order_tac.
  have s2r: (inc  (sup r x y) (substrate r)) by order_tac.
  have [le1' le2' le3'] := (lattice_sup_pr lr xE s1r).
  have [le4' le5' le6'] := (lattice_sup_pr lr s2r zE). 
  apply: (order_antisymmetry or).
    apply: le3'.
      apply: (order_transitivity or le1 le4').
    apply: le6 => //; apply: (order_transitivity or le2 le4'). 
  apply: le6'.
    apply: le3 => //.
    apply: (order_transitivity or le4 le2'). 
  apply: (order_transitivity or le5 le2').
have ia: (forall x y z, inc x E->  inc y E -> inc z E ->
        inf r x (inf r y z) = inf r (inf r x y) z).
  move => x y z xE yE zE.
  have [le1 le2 le3] := (lattice_inf_pr lr xE yE). 
  have [le4 le5 le6] := (lattice_inf_pr lr yE zE).
  have s1r: (inc  (inf r y z) (substrate r)) by order_tac.
  have s2r: (inc  (inf r x y) (substrate r)) by order_tac.
  have [le1' le2' le3'] := (lattice_inf_pr lr xE s1r). 
  have [le4' le5' le6']:=  (lattice_inf_pr lr s2r zE).
  apply: (order_antisymmetry or).
    apply: le6'.
      apply: le3  => //. 
        apply: (order_transitivity or le2' le4).
      apply: (order_transitivity or le2' le5).
  apply: le3'.
    apply: (order_transitivity or le4' le1). 
  apply: le6 => //; apply: (order_transitivity or le4' le2).  
have sxx:forall x, inc x E -> sup r x x = x.
  by move => x xE; apply: sup_comparable1 => //; order_tac.
have ixx:forall x, inc x E -> inf r x x = x.
  by move => x xE; apply: inf_comparable1 => //; order_tac.
split.
  move => x y xE yE; move: (lattice_sup_pr lr xE yE) => [le1 e2 le3]. 
  rewrite /E;order_tac.
split. 
  move => x y xE yE; move: (lattice_inf_pr lr xE yE) => [le1 le2 le3]. 
  rewrite /E;order_tac.
split. 
  move => x y xE yE; move: (lattice_inf_pr lr xE yE) => [le1 le2 le3]. 
  apply:  (sup_comparable1 or le2). 
split.
  move => x y xE yE; move: (lattice_sup_pr lr xE yE) => [le1 le2 le3]. 
  rewrite inf_C; apply:  (inf_comparable1 or le2). 
split; [ exact | split; [exact | split ; [exact | split => //]]].
split.
  by move => x y xE yE; rewrite sup_C sa // sxx.
by move => x y xE yE; rewrite inf_C ia // ixx.
Qed.

Lemma sup_monotone a b c: inc a E -> gle r b c-> gle r (sup r a b)  (sup r a c).
Proof.
move=>  asr bc.
move: (lattice_sup_pr lr asr (arg1_sr bc)).
move: (lattice_sup_pr lr asr (arg2_sr bc)).
move: lr => [or _] [p1 p2 _][_ _ p6].
by apply: p6; [ apply: p1 | apply: order_transitivity p2].
Qed.

Lemma inf_monotone a b c: inc a E -> gle r b c-> gle r (inf r a b) (inf r a c).
Proof.
move=> asr bc.
move: (lattice_inf_pr lr asr (arg1_sr bc)).
move: (lattice_inf_pr lr asr (arg2_sr bc)).
move: lr => [or _] [_ _ p6] [p1 p2 _].
by apply: p6; [ apply: p1 |  apply: order_transitivity bc].
Qed.

Lemma lattice_finite_sup1 X x a:
  sub X E -> least_upper_bound r X x -> inc a E ->
  least_upper_bound r (X +s1 a) (sup r x a).
Proof.
move=>  Xsr lub asr.
have or: (order r) by move: lr => [ok _].
have st: (sub (X +s1 a) (substrate r)) by apply: setU1_sub.
move /(lubP or Xsr): lub =>  [[lu1 lu2] lu3].
have [p1 p2 p3] := (lattice_sup_pr lr lu1 asr).
apply /(lubP or st); split.
  split; first by order_tac. 
  move=> y; case /setU1_P => h;[move: (lu2 _ h)=> h'; order_tac| ue].
move=>z [z1 z2]; apply:p3;[apply: lu3; split => //t tx |];apply: z2; fprops.
Qed.

Lemma lattice_finite_inf1 X x a:
  sub X E -> greatest_lower_bound r X x -> inc a E ->
  greatest_lower_bound r (X +s1 a) (inf r x a).
Proof.
move=>  Xsr lub asr.
have or: (order r) by move: lr => [ok _].
have st: (sub (X +s1 a) (substrate r)) by apply: setU1_sub.
move /(glbP or Xsr): lub =>  [[lu1 lu2] lu3].
have [p1 p2 p3] := (lattice_inf_pr lr lu1 asr).
apply /(glbP or st); split.
  split; first by order_tac. 
  move=> y; case /setU1_P => h;[move: (lu2 _ h)=> h'; order_tac| ue].
move=>z [z1 z2]; apply: p3;[apply: lu3;split => // t tx |];apply: z2; fprops.
Qed.

End LatticeProps.


Definition distributive_lattice1 r :=
  forall x y z, inc x (substrate r) ->inc y (substrate r) ->
    inc z (substrate r) ->
    sup r x (inf r y z) = inf r (sup r x y) (sup r x z).

Definition distributive_lattice2 r :=
  forall x y z, inc x (substrate r) ->inc y (substrate r) ->
    inc z (substrate r) ->
    inf r x (sup r y z) = sup r (inf r x y) (inf r x z).
Definition distributive_lattice3 r :=
  forall x y z, inc x (substrate r) ->inc y (substrate r) ->
    inc z (substrate r) ->
    sup r (inf r x y) (sup r (inf r y z) (inf r z x)) =
    inf r (sup r x y) (inf r (sup r y z) (sup r z x)).
Definition distributive_lattice4 r :=
  forall x y z, inc x (substrate r) ->inc y (substrate r) ->
    inc z (substrate r) ->
    gle r z x -> sup r z (inf r x y) = inf r x (sup r y z).
Definition distributive_lattice5 r:=
  forall x y z, inc x (substrate r) ->inc y (substrate r) ->
    inc z (substrate r) ->
    gle r (inf r z (sup r x y)) (sup r x (inf r y z)).
Definition distributive_lattice6 r :=
  forall x y z, inc x (substrate r) ->inc y (substrate r) ->
    inc z (substrate r) ->
    inf r (sup r x y) (sup r z (inf r x y))
    = sup r (inf r x y) (sup r (inf r y z) (inf r z x)).

Lemma total_order_dlattice r:
  total_order r -> distributive_lattice1 r.
Proof.
move=>  [or tor] a b c ar br cr.
case: (tor _ _ ar br) => ab.
    rewrite (sup_comparable1 or ab); case: (tor _ _ ar cr) => ac.
      rewrite (sup_comparable1 or ac); case: (tor _ _ br cr) => bc.
      by rewrite (inf_comparable1 or bc) (sup_comparable1 or ab).
    by rewrite(inf_C r b c) (inf_comparable1 or bc)(sup_comparable1 or ac).
  rewrite (sup_C r a c)(sup_comparable1 or ac). 
  rewrite (inf_C r b a) (inf_comparable1 or ab).
  have cb: (gle r c b) by order_tac.
  rewrite (inf_C r b c) (inf_comparable1 or cb).
  by rewrite (sup_C r a c) (sup_comparable1 or ac).
rewrite (sup_C r a b) (sup_comparable1 or ab).
case: (tor _ _ ar cr) => ac.
   rewrite (sup_comparable1 or ac)  (inf_comparable1 or ac).
   have bc: (gle r b c) by order_tac.
   by rewrite (inf_comparable1 or bc)  (sup_C r a b) (sup_comparable1 or ab).
rewrite (sup_C r a c) (sup_comparable1 or ac).
have aa: (gle r a a) by order_tac.
rewrite (inf_comparable1 or aa). 
case: (tor _ _ br cr) => bc.
  by rewrite (inf_comparable1 or bc)  (sup_C r a b) (sup_comparable1 or ab).
rewrite  (inf_C r b c) (inf_comparable1 or bc).
by rewrite  (sup_C r a c) (sup_comparable1 or ac).
Qed.


Section DistributiveLattice.
Variable r: Set.
Hypothesis lr: lattice r.

Lemma distributive_lattice_prop1: 
  ( (distributive_lattice1 r -> distributive_lattice3 r) /\
    (distributive_lattice2 r -> distributive_lattice3 r)).
Proof. 
move:(lattice_props lr).
set (E:= substrate r).
move => [sE [iE [sixy [isxy [sxyz [ixyz [sxx [ixx [sxyx ixyx]]]]]]]]].
split.
  move=> d1 x y z xE yE zE.
  move: (iE _ _ yE zE) (sE _ _ xE yE) => iyzE sxyE.
  rewrite (d1 _ _ _ iyzE zE xE) (sup_C r (inf r y z) x).
  rewrite (d1 _ _ _ xE yE zE) (sup_C r x z) (sixy _ _ yE zE).
  set (sxy :=sup r x y); set (syz:=sup r y z); set (szx:= sup r z x).
  have ->:(inf r z (inf r sxy szx) = inf r z sxy). 
    rewrite (inf_C r sxy szx) (ixyz _ _ _ zE (sE _ _ zE xE)  sxyE). 
    rewrite (inf_C r z  (sup r z x)) (sup_C r z x) (isxy _ _ xE zE) //. 
  rewrite (d1 _ _ _ (iE _ _ xE yE) zE sxyE) (sup_C r _ z).
  rewrite (d1 _ _ _ zE xE yE) (sup_C r z y) (sup_C r (inf r x y) _).
  rewrite (d1 _ _ _ sxyE xE yE).
  rewrite (sxyx _ _ xE yE) {2} (sup_C r x y) (sxyx _ _ yE xE).
  rewrite (sup_C r y x) (ixx _ sxyE) inf_C (inf_C r syz szx) //.
move=> d1 x y z xE yE zE.
move: (sE _ _ yE zE) (iE _ _ xE yE) => syzE ixyE.
rewrite (d1 _ _ _ syzE zE xE) (inf_C r (sup r y z) x).
rewrite (d1 _ _ _ xE yE zE) (inf_C r x z) (isxy _ _ yE zE).
set (ixy := inf r x y); set (iyz:= inf r y z); set (izx:= inf r z x).
have ->:(sup r z (sup r ixy izx) = sup r z ixy). 
  rewrite (sup_C r ixy izx) (sxyz _ _ _ zE (iE _ _ zE xE)  ixyE). 
  rewrite (sup_C r z (inf r z x)) (inf_C r z x) (sixy _ _ xE zE) //. 
rewrite (d1 _ _ _ (sE _ _ xE yE) zE ixyE) (inf_C r _ z).
rewrite (d1 _ _ _ zE xE yE) (inf_C r z y) (inf_C r (sup r x y) _).
rewrite (d1 _ _ _ ixyE xE yE).
rewrite (ixyx _ _ xE yE) {2} (inf_C r x y) (ixyx _ _ yE xE).
rewrite  (inf_C r y x) (sxx _ ixyE) sup_C (sup_C r iyz izx) //.
Qed.

Lemma distributive_lattice_prop2:
  [/\ (distributive_lattice3 r -> distributive_lattice4 r),
    (distributive_lattice3 r -> distributive_lattice1 r) &
    (distributive_lattice3 r -> distributive_lattice2 r)].
Proof.
move:(lattice_props lr).
set (E:= substrate r).
move: (lr) => [or _].
move => [sE [iE [sixy [isxy [sxyz [ixyz [sxx [ixx [sxyx ixyx]]]]]]]]].
have p1: (distributive_lattice3 r -> distributive_lattice4 r). 
  move => h x y z xE yE zE zx.
  move: (h _ _ _ xE yE zE).
  rewrite (inf_comparable1 or zx)(sup_comparable1 or zx).
  rewrite (sixy _ _ yE zE) (inf_C r (sup r y z) x).
  rewrite (ixyz _ _ _ (sE _ _ xE yE) xE (sE _ _ yE zE)).
  rewrite (sup_C r x y) (isxy _ _ yE xE) sup_C//.
split; first by exact.
  move=> d3 x y z xE yE zE.
  move: (d3 _ _ _ xE yE zE) => ab;move: (f_equal (sup r x) ab).
  set (t := sup r x (inf r (sup r x y) (inf r (sup r y z) (sup r z x)))).
  move: (iE _ _ xE yE) (iE _ _ yE zE) (iE _ _ zE xE) => ixyE iyzE izxE.
  rewrite (sxyz _ _ _ xE ixyE (sE _ _ iyzE izxE)).
  rewrite (sup_C r x _) (inf_C r x y) (sixy _ _ yE xE).
  rewrite (sup_C r (inf r y z) (inf r z x)).
  rewrite (sxyz _ _ _ xE izxE iyzE) (sup_C r x (inf r z x)) (sixy _ _ zE xE).
  move=> ->.
  rewrite /t.
  rewrite (sup_C r x z); set sxy:= sup r x y; set szx:= sup r z x.
  have xsxy:gle r x sxy  by move: (lattice_sup_pr lr xE yE)=> [q1 q2 q3].
  have sxyE: inc sxy (substrate r) by order_tac.
  rewrite ((p1 d3) _ _ _ sxyE (iE _ _ (sE _ _ yE zE) (sE _ _ zE xE)) xE xsxy).
  apply: f_equal.  
  rewrite sup_C inf_C -/szx.
  have xsrx:gle r x szx by move: (lattice_sup_pr lr zE xE)=> [q1 q2 q3].
  have szxE: inc szx (substrate r) by order_tac.
  rewrite ((p1 d3) _ _ _ szxE  (sE _ _ yE zE) xE xsrx).
  rewrite -(sxyz _ _ _ yE zE xE) -/szx inf_C;  apply: isxy => //.
move=> d3 x y z xE yE zE.
move: (d3 _ _ _ xE yE zE) => ab;move: (f_equal (inf r x) ab).
set (t := inf r x (sup r (inf r x y) (sup r (inf r y z) (inf r z x)))).
move: (sE _ _ xE yE) (sE _ _ yE zE) (sE _ _ zE xE) => sxyE syzE szxE.
rewrite (ixyz _ _ _ xE sxyE (iE _ _ syzE szxE)).
rewrite (inf_C r x _) (sup_C r x y) (isxy _ _ yE xE).
rewrite (inf_C r (sup r y z) (sup r z x)).
rewrite (ixyz _ _ _ xE szxE syzE) (inf_C r x (sup r z x)) (isxy _ _ zE xE).
move=> <-; rewrite /t.
rewrite (inf_C r x z); set ixy:= inf r x y; set izx:= inf r z x.
have xsxy:gle r ixy x  by move: (lattice_inf_pr lr xE yE)=> [q1 q2 q3].
have ixyE: inc ixy (substrate r) by order_tac.
rewrite sup_C.
rewrite -((p1 d3) _ _ _ xE (sE _ _ (iE _ _ yE zE) (iE _ _ zE xE)) ixyE xsxy).
apply: f_equal.
have xsrx:gle r izx x by move: (lattice_inf_pr lr zE xE)=> [q1 q2 q3].
have izxE: inc izx (substrate r) by order_tac.
rewrite -((p1 d3) _ _ _ xE (iE _ _ yE zE) izxE xsrx).
rewrite inf_C -(ixyz  _ _ _ yE zE xE) .
rewrite -/izx sup_C  sixy //.
Qed.

Lemma distributive_lattice_prop3:
  (distributive_lattice3 r <-> distributive_lattice5 r).
Proof. 
move: (lr) => [or _].
move:(lattice_props lr) =>/=.
set (E:= substrate r).
move => [sE [iE [sixy [isxy [sxyz [ixyz [sxx [ixx [sxyx ixyx]]]]]]]]].
split => aux.
   move: (distributive_lattice_prop2) => [p1 p2 p3].
   move=> x y z xE yE zE.
   rewrite (p3 aux) // (inf_C r z y).
   move: (iE _ _ yE zE) (iE _ _ zE xE); set b:= inf r y z.
   move=> bE izxE.
   move: (lattice_sup_pr lr xE bE) => [q1 q2 q3]. 
   move: (lattice_sup_pr lr izxE bE)=> [_ _]; apply => //.
   apply: order_transitivity q1 => //.
   by move: (lattice_inf_pr lr zE xE) => [r1 r2 r3].
move: (distributive_lattice_prop1) => [h _]; apply: h.
move => x y z xE yE zE.
move: (iE _ _ yE zE) (sE _ _ xE zE) (sE _ _ xE yE) => iyzE sxzE sxyE.
apply: (order_antisymmetry or).
  move: (lattice_sup_pr lr xE (iE _ _ yE zE)) => [q1 q2 q3].
  move: (lattice_inf_pr lr yE zE) => [r1 r2 _].
  move: (lattice_inf_pr lr sxyE sxzE) => [_ _]; apply.
    move: (lattice_sup_pr lr xE yE) => [p1 p2 p3]. 
    apply: q3 => //; apply: order_transitivity p2 => //.
  move: (lattice_sup_pr lr xE zE)  => [p1 p2 p3]. 
  apply: q3 => //; apply: order_transitivity p2  => //.
move: (aux _ _ _ xE yE zE).
move: (aux _ _ _ xE zE (sE _ _ xE yE)).
set (a:= inf r (sup r x y) (sup r x z)).
set (b:= sup r x (inf r y z)).
set (c:= inf r z (sup r x y)).
move=> le1 le2.
move: (lattice_sup_pr lr xE iyzE); rewrite -/b; move=> [le3 _ _].
move: (lattice_sup_pr lr xE (iE _ _ zE sxyE) ); rewrite -/c; move=> [_ _ hc].
apply: (order_transitivity or le1 (hc _ le3 le2)).
Qed. 

Lemma distributive_lattice_prop4:
  (distributive_lattice3 r <-> distributive_lattice6 r).
Proof.
move: (lr) => [or _].
move:(lattice_props lr) =>/=.
set (E:= substrate r).
move => [sE [iE [sixy [isxy [sxyz [ixyz [sxx [ixx [sxyx ixyx]]]]]]]]].
split => aux.
  move=> x y z xE yE zE.
  move: (sE _ _ xE yE)(iE _ _ xE yE) => sxyE ixyE.
  move: (distributive_lattice_prop2) => [_ _ il2]. 
  rewrite ((il2 aux) _ _ _ sxyE zE ixyE).
  rewrite (inf_C r (sup r x y) z) ((il2 aux) _ _ _ zE xE yE)(inf_C r y z).
  have ->: (inf r (sup r x y) (inf r x y) = inf r x y).
    rewrite inf_C; apply: inf_comparable1 => //.
    move: (lattice_sup_pr lr xE yE) (lattice_inf_pr lr xE yE).
    move=> [p1 _ _] [p2 _ _]; order_tac.
  rewrite sup_C; apply: f_equal; rewrite sup_C //.
apply /distributive_lattice_prop3; move=> x y z xE yE zE.
rewrite (inf_C r z (sup r x y)).
move: (aux _ _ _ xE yE zE).
move: (sE _ _ xE yE)(iE _ _ xE yE); set (b:= sup r x y); set (xy:= inf r x y).
move=> bE xyE.
move: (lattice_inf_pr lr bE zE)=> [z1 z2 z3].
move: (lattice_sup_pr lr zE xyE)=> [w1 w2 w3].
set A:= inf r _ _; set B := sup r _ _.
have l1: gle r (inf r (sup r x y) z) A.
  rewrite /A;move: (lattice_inf_pr lr bE (sE _ _ zE xyE)). 
  move=> [q1 q2 q3]; apply: q3 => //; order_tac.
move: (iE _ _ yE zE)(iE _ _ zE xE); set (yz:= inf r y z); set (zx:= inf r z x).
move=> yzE zxE.
have l2: gle r B (sup r x yz).
  rewrite /B.
  move: (lattice_sup_pr lr xE yzE) => [q1 q2 q3].
  move: (lattice_sup_pr lr xyE (sE _ _ yzE zxE))=> [_ _]; apply.
    move: (lattice_inf_pr lr xE yE) => [h _ _]; order_tac. 
  move: (lattice_sup_pr lr yzE zxE) => [_ _ ]; apply;first by exact.  
  move: (lattice_inf_pr lr zE xE) => [_ h _]; order_tac. 
move=> AB; rewrite AB in l1; order_tac.
Qed.
 
End DistributiveLattice.

Theorem total_order_monotone_injective f r r':
  total_order r -> strict_monotone_fun f r r' -> injection f.
Proof.
move=> tor.
case;move=>[or or' [ff sr sr'] hyp]; split=>// x y; rewrite sr =>  xs ys sW.
  by case:(total_order_pr1 tor xs ys) => // /hyp  [_]; rewrite sW.
by case:(total_order_pr1 tor xs ys) => // /hyp  [_]; rewrite sW.
Qed.

Theorem total_order_increasing_morphism f r r':
  total_order r -> strict_increasing_fun f r r' -> order_morphism f r r'.
Proof.
move=> tor si.  
have ijf: (injection f) . 
  by apply: (@total_order_monotone_injective f r r') =>//;left.
have ic:= (strict_increasing_w si).
move: si ic =>  [or or' [ff sr sr'] sif] [_ _ _ nif].
split => // x y xs ys; split; first by apply: nif.
rewrite sr in xs ys.
case: (total_order_pr2 tor ys xs) => // h.
move: (sif  _ _ h)=> p1 p2; order_tac.
Qed.

(** If the source is totally ordered, 
    an increasing injective function is a morphism *)

Lemma total_order_morphism f r r':
  total_order r -> order r' ->
  injection f ->  substrate r = source f -> substrate r' = target f ->
  {inc source f &, fincr_prop f r r'} ->
  order_morphism f r r'.
Proof.
move=> to or' [ff injf] sf tf incf.
apply: total_order_increasing_morphism  => //.
move: to => [or _]; split => // x y [lexy nxy].
move:(arg1_sr lexy)(arg2_sr lexy); rewrite sf => xsf ysf.
by split; [apply: incf | dneg aa; apply: injf]. 
Qed.

Lemma total_order_isomorphism f r r':
  total_order r -> order r' ->
  bijection f ->  substrate r = source f -> substrate r' = target f ->
  {inc source f &, fincr_prop f r r'} ->
  order_isomorphism f r r'.
Proof.
move=> to or' bjf sf tf incf.
move: (bjf) => [injf _].
have: (order_morphism f r r') by apply: total_order_morphism.
by move=> [p1 p2 [p3 p4 p5] p6].
Qed.


Theorem sup_in_total_order r X x: total_order r -> sub X (substrate r)->
  (least_upper_bound r X x <-> (upper_bound r X x /\ 
    (forall y, glt r y x -> exists z, [/\ inc z X, glt r y z & gle r z x]))).
Proof. 
move=> tor Xs.
have or: order r by move: tor=> [].
split.  
  move /(lubP or Xs) => [ub lub]; split=>// y yx.
  have nu: (~ (upper_bound r X y)). 
    by move=> ys; move: (lub _ ys)=> xy; order_tac.
  have ysr: (inc y (substrate r)) by order_tac.
  have [z zX yz]: (exists2 z, inc z X & glt r y z).
    ex_middle bad; case: nu; split => //.
    move=> u ux; case: (total_order_pr2 tor ysr (Xs _ ux)) =>// aux. 
    case: bad; ex_tac.
  by exists z; split => //; move: ub=> [_]; apply. 
move => [pa pb]; apply/(lubP or Xs); split => //.
move=> z ubz.
have xs:inc x (substrate r) by case: pa.
have zs:inc z (substrate r) by case: ubz.
case: (total_order_pr2 tor zs xs) =>// /pb [t [tX yt _]].
case: (not_le_gt or ((proj2 ubz) _ tX) yt).
Qed.

Theorem inf_in_total_order r X x: total_order r -> sub X (substrate r)->
  (greatest_lower_bound r X x <-> (lower_bound r X x /\ 
    (forall y, glt r x y -> exists z, [/\ inc z X, glt r z y &  gle r x z]))).
Proof. 
move=>  tor Xs.
have or: order r by move: tor=> []. 
split.  
  move /(glbP or Xs) => [ub lub]; split=>// y yx.
  have nu: (~ (lower_bound r X y)). 
    by move=> ys; move: (lub _ ys)=> xy; order_tac.
  have ysr: (inc y (substrate r)) by  order_tac.
  have [z zX yz]: (exists2 z, inc z X & glt r z y).
    ex_middle bad;case: nu; split =>// u ux.
    case: (total_order_pr2 tor (Xs _ ux) ysr) =>// aux.
    case: bad; ex_tac.
  by exists z; split => //; move: ub=> [_]; apply. 
move => [ub lub]; apply/(glbP or Xs); split => // z ubz.
have xs:inc x (substrate r) by case: ub.
have zs:inc z (substrate r) by case: ubz.
case: (total_order_pr2 tor xs zs) =>// /lub [t [tX yt tx]].
case: (not_le_gt or ((proj2 ubz) _ tX) yt).
Qed.

(** ** Intervals *)

Definition interval_oo r a b :=Zo(substrate r)(fun z => glt r a z /\ glt r z b).
Definition interval_oc r a b :=Zo(substrate r)(fun z => glt r a z /\ gle r z b).
Definition interval_ou r a  := Zo(substrate r)(fun z => glt r a z).
Definition interval_co r a b := Zo(substrate r)(fun z=> gle r a z /\ glt r z b).
Definition interval_cc r a b := Zo(substrate r)(fun z=> gle r a z /\ gle r z b).
Definition interval_cu r a  := Zo (substrate r)(fun z => gle r a z).
Definition interval_uo r b := Zo (substrate r) (fun z =>  glt r z b).
Definition interval_uc r b := Zo (substrate r) (fun z => gle r z b).
Definition interval_uu r := Zo (substrate r) (fun z => True).

Definition closed_interval r x := exists a b,
  [/\ inc a (substrate r), inc b (substrate r), gle r a b &
  x = interval_cc r a b].
Definition open_interval r x := exists a b,
  [/\ inc a (substrate r), inc b (substrate r), gle r a b &
  x = interval_oo r a b].
Definition semi_open_interval r x := exists a b,
  [/\ inc a (substrate r), inc b (substrate r),  gle r a b &
  (x = interval_oc r a b \/ x = interval_co r a b)].
Definition bounded_interval r x := closed_interval r x \/
  open_interval r x \/ semi_open_interval r x.
Definition left_unbounded_interval r x := 
  exists2 b, inc b (substrate r)& (x = interval_uc r b \/ x = interval_uo r b).
Definition right_unbounded_interval r x := 
  exists2 a, inc a (substrate r)& (x = interval_cu r a \/ x = interval_ou r a).
Definition unbounded_interval r x :=
  left_unbounded_interval r x \/ right_unbounded_interval r x  \/
  x = interval_uu r.
Definition interval r x :=  
  bounded_interval r x  \/ unbounded_interval r x.

Lemma the_least_interval r a b: order r ->
  gle r a b -> (the_least_induced r (interval_cc r a b)) = a.
Proof. 
move=> or ab.
have sab:  (sub (interval_cc r a b) (substrate r)) by apply: Zo_S.
have asr: inc a (substrate r) by apply: (arg1_sr ab).
have aicc: inc a (interval_cc r a b).
  by apply: Zo_i =>//;  split=>//; order_tac. 
have [or' sr]:= (iorder_osr or sab).
apply: the_least_pr2; [exact | hnf;rewrite sr].
split =>//;move=> x xi; apply/iorder_gle0P => //.
by move/Zo_P: xi => [_ []].
Qed.

Lemma the_greatest_interval r a b: order r ->
  gle r a b -> the_greatest (induced_order r (interval_cc r a b)) = b.
Proof.
move=> or ab.
have sab:  (sub (interval_cc r a b) (substrate r))  by apply: Zo_S. 
have asr: inc b (substrate r) by apply: (arg2_sr ab).
have aicc: inc b (interval_cc r a b).
  by apply: Zo_i =>//;  split=>//; order_tac. 
have [or' sr]:= (iorder_osr or sab).
apply: the_greatest_pr2; [exact | hnf;rewrite sr].
split =>//;move=> x xi; apply/iorder_gle0P => //.
by move/Zo_P: xi => [_ []].
Qed.


Lemma nonempty_closed_interval r x: 
  order r -> closed_interval r x -> nonempty x.
Proof. 
move=> or [a [b [asr bsr ab xab]]]. 
exists a; rewrite xab; apply: Zo_i =>//.
by split=>//; order_tac. 
Qed.

Lemma singleton_interval r a:
  order r -> inc a (substrate r) -> singletonp (interval_cc r a a). 
Proof. 
move=> or asr; exists a; apply: set1_pr. 
  by apply:Zo_i=> //;split => //; order_tac. 
move=> z /Zo_P [_ [p1 p2]]; order_tac.
Qed.

Lemma empty_interval r a:
  order r -> inc a (substrate r) -> 
  [/\ empty (interval_co r a a),  empty (interval_oc r a a) &
    empty (interval_oo r a a)]. 
Proof. 
move=> or asr; split => // y /Zo_hi [p1 p2]; order_tac.
Qed.

Lemma setI_i1 r x:
  interval r x -> x \cap (interval_uu r) = x.
Proof. 
move=> hyp.
have ->: interval_uu r = substrate r.
  apply: extensionality; first by apply: Zo_S. 
  by move=> t tr; apply /Zo_P.
suff: sub x (substrate r).
  move=> h; apply: extensionality; first by apply: subsetI2l.
  by move=> t tx; apply: setI2_i=>//; apply: h. 
case: hyp.
  case; first by  move=> [a [b [_ _ _ ->]]] ; apply: Zo_S.
  case. 
    move=> [a [b [_ _ _ ->]]]; apply: Zo_S.
  move=> [a [b [_ _ _]]]. 
  case; move=> ->; apply: Zo_S.
case; first by move=> [a _]; case; move=> ->; apply: Zo_S.
case; first by move=> [a _]; case; move=> ->; apply: Zo_S.
move=> ->; apply: Zo_S.
Qed.

Definition lu_interval r x :=
   x = interval_uu r \/ left_unbounded_interval r x.
Definition ru_interval r x :=
   x = interval_uu r \/ right_unbounded_interval r x.

Ltac zztac2 v  := set_extens v ; 
   try (move/setI2_P=>[] /Zo_P [pa pb] /Zo_P [pc pd]; apply: Zo_i => //);
   try (move /Zo_P  => [ pa pb]; apply /setI2_P; split; apply: Zo_i => //).

Lemma setI_i2 r x:
  interval r x -> 
  (exists u v, [/\ lu_interval r u, ru_interval r v &
    u \cap v = x]).
Proof. 
move=> ix; move: (ix).
have p1: forall b, inc b (substrate r) -> lu_interval r (interval_uc r b).
  by move=> b hb; right; exists b => //; left.
have p2: forall b, inc b (substrate r) -> lu_interval r (interval_uo r b).
  by move=> b hb; right; exists b => //; right.
have p3: forall b, inc b (substrate r) -> ru_interval r (interval_cu r b).
  by move=> b hb; right; exists b => //; left.
have p4: forall b, inc b (substrate r) -> ru_interval r (interval_ou r b).
  by move=> b hb; right; exists b => //; right.
case.
  case.  
    move=> [a [b [au bu ab xab]]].
    exists (interval_uc r b), (interval_cu r a); split; fprops.
    by rewrite xab; zztac2 y; case :pb.
  case.
    move=> [a [b [au bu ab xab]]]. 
    exists (interval_uo r b), (interval_ou r a); split; fprops.
    by rewrite xab; zztac2 y; case: pb.
  move=> [a [b [au bu ab xab]]]. 
  case: xab=> ->.
    exists (interval_uc r b), (interval_ou r a); split; fprops.
    by zztac2 y; case: pb.
  exists (interval_uo r b), (interval_cu r a); split; fprops.
  by zztac2 y; case: pb.
case.
  move=>[a au xa].
  exists x, (interval_uu r);split.
  + by case: xa => ->; fprops.
  + by left.
  + by apply: setI_i1.
case.
  move=>[a au xa].
  exists (interval_uu r), x; split.
  + by left.
  + case: xa =>  ->; fprops.
  + by rewrite setI2_C; apply: setI_i1.
move=> h; exists x, x; rewrite h.
split; try (left => //);apply: setI_i1; ue.
Qed.

Lemma setI_i3 r x y: lattice r ->
  left_unbounded_interval r x -> left_unbounded_interval r y -> 
  left_unbounded_interval r (x \cap y).
Proof. 
move=> lar  [a asr xa][b bsr yb].
have or: order r by move: lar=> [].
move: (lattice_inf_pr lar asr bsr). 
set (u:=inf r a b); set (v:= sup r a b).
move=> [ua ub uab]. 
exists u; first by order_tac.
case: xa => ->.
  case: yb => ->.
    left; zztac2 z; [ by apply:uab | order_tac | order_tac ].
  case: (p_or_not_p (glt r u b)).
  left; zztac2 z; try order_tac; apply: uab => //; order_tac.
  move=> ltuv; right; zztac2 z; try order_tac.
    split; first by apply: uab => //; order_tac.
    by move=> zu; rewrite zu in pd; case: ltuv. 
  move: pb => [pb _]; order_tac.
case: yb=> ->.
  case: (p_or_not_p (glt r u a)) => qe.
  left; zztac2 z; try order_tac;apply: uab => //; order_tac. 
  right; zztac2 z;try order_tac. 
    split; first by apply: uab => //; order_tac.
    by move=> zu; rewrite zu in pb; case: qe. 
  move: pb => [pb _]; order_tac.
case: (p_or_not_p (glt r u a /\ glt r u b)).
  move=> [p1 p2].
  left; zztac2 z; try order_tac; apply: uab => //; order_tac.
move=> p1p2; right; zztac2 z;  try order_tac; split.
  apply: uab => //; order_tac.
by move=> zu; rewrite zu in pb pd; case: p1p2; split. 
Qed.

Theorem setI_interval r x y:
  lattice r -> interval r x -> interval r y ->
  interval r (x \cap y).
Proof. 
move=> lar ix iy.
have or: order r by move: lar=> [].
move: (setI_i2 ix) (setI_i2 iy).
move=> [a [b [lua rub abx]]][c [d [luc rud cdy]]].
rewrite -abx -cdy setI2_ACA.
have lu1: lu_interval r (a \cap c).
  case: lua.
     move=>->; rewrite setI2_C setI_i1 //. 
     right; hnf; case: luc; fprops.
  case: luc. 
    move=>-> p; rewrite setI_i1;[ by right| by right; left]. 
  by  move=> p1 p2; right; apply: setI_i3.
have ru1: ru_interval r (b \cap d). 
  case: rub.
     move=>->; rewrite setI2_C setI_i1 //. 
     right; hnf; case: rud; fprops.
  move=> irub; case: rud.
     move=>->; rewrite  setI_i1 //; [by right | by right; right; left].
  move=> irud.
  move: (opp_osr  or) => [ha hb].
  have Ha: forall a, interval_cu r a = interval_uc (opp_order r) a.
   move=> t; set_extens u; move/Zo_P => []; aw => pa pb;
      apply:Zo_i; try ue; by apply/igraph_pP.
  have Hb: forall a, interval_ou r a = interval_uo (opp_order r) a.
    move=> t; set_extens u; move/Zo_P => []; aw; move => pa [p pc];
      apply:Zo_i; try ue; split; try (apply/igraph_pP => //); fprops.
  have Hc: left_unbounded_interval (opp_order r) b.
    move:irub => [e es be]; case: be => ->; exists e;try ue; fprops.
  have Hd: left_unbounded_interval (opp_order r) d.
    move:irud => [e es be]; case: be => ->; exists e; try ue;fprops.
  have He :lattice (opp_order r) by apply: lattice_opposite. 
  move: (setI_i3 He Hc Hd) => [e es].
  rewrite -Ha -Hb; move: es; try ue; move => es//. 
  case => ->; right; exists e; try ue;fprops.
have i1: interval r  (a \cap c) by right; hnf; case: lu1; fprops.
have i2: interval r  (b \cap d) by right; hnf; case: ru1; fprops.
case: lu1.
  move=> ->; rewrite setI2_C setI_i1 //. 
move=> lu2; case: ru1; first by move=>->;rewrite  setI_i1 =>//. 
 move=> ru2.
left.
move: lu2 ru2 => [e es ace][f fs bdf].
case: (p_or_not_p (gle r f e)) => fe.
  case: ace=> ->.
    case: bdf=> ->.
      by left; exists f, e; split => //; zztac2 t; case: pb.
    by right;right;exists f, e; split => //; left; zztac2 t; case: pb.
  case: bdf=> ->.
    by right;right;exists f, e; split => //; right; zztac2 t; case: pb.
  by right; left ;exists f, e; split => //; zztac2 t; case: pb.
suff: (empty  ((a \cap c) \cap (b \cap d))).
  move=> h.  
  move:(empty_interval or fs) => [_ _ oo]; right; left. 
  exists f, f; split => //; try order_tac => //.
  by set_extens t => te; [ case: (h t) | case: (oo t)].
move=> t /setI2_P [ti1 ti2]; case: fe.
have p1: gle r t e. 
   move: ti1; case: ace=> ->;  move/Zo_P => [pa pb] //; order_tac.
have p2: gle r f t. 
  move: ti2; case: bdf=> ->; move/Zo_P => [pa pb] //; order_tac.
order_tac.
Qed.

End Border.

Export Border. 
