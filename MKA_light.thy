(* 
Title: A Light-Weight Component for Modal Kleene Algebra
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Modal Kleene algebra light\<close>

theory "MKA_light"
  imports KA_light

begin

text \<open>This is a light-weight theory for Kleene algebra with domain and modal Kleene algebra. It could eventually be replaced by the AFP entry.\<close>

subsection \<open>Domain semirings\<close>

class dom_op = 
  fixes dom :: "'a \<Rightarrow> 'a"

class cod_op =
  fixes cod :: "'a \<Rightarrow> 'a"

class domain_semiring = dioid + dom_op +
  assumes d_absorb: "x \<le> dom x \<cdot> x"
  and d_local [simp]: "dom (x \<cdot> dom y) = dom (x \<cdot> y)"
  and d_add [simp]: "dom (x + y) = dom x + dom y"
  and d_subid: "dom x \<le> 1"
  and d_zero [simp]: "dom 0 = 0"

begin

lemma d_absorb_eq [simp]: "dom x \<cdot> x = x"
  using local.d_absorb local.d_subid local.dual_order.antisym local.mult_iso by fastforce

lemma d_idem [simp]: "dom x \<cdot> dom x = dom x"
  by (metis d_absorb_eq local.d_local local.mult_1_left)

lemma d_invol [simp]: "dom (dom x) = dom x"
  by (metis d_absorb_eq d_idem local.d_local)

lemma d_id [simp]: "dom 1 = 1"
  by (metis d_absorb_eq local.mult_1_right)

lemma d_export [simp]: "dom (dom x \<cdot> y) = dom x \<cdot> dom y"
  apply (rule order.antisym)
  apply (metis d_absorb_eq d_id d_idem local.d_local local.d_add local.d_subid local.distl local.distr local.mult.monoid_axioms local.mult_1_right local.mult_iso local.order_def monoid.left_neutral)
  by (metis d_absorb_eq local.d_local local.d_subid local.mult_1_right local.mult_iso local.mult_isol)

lemma d_export_var [simp]: "dom x \<cdot> dom (x \<cdot> y) = dom (x \<cdot> y)"
  by (metis d_absorb_eq d_export mult_assoc)

lemma d_iso: "x \<le> y \<Longrightarrow> dom x \<le> dom y"
  by (metis local.d_add local.order_def)

lemma dadd_closed [simp]: "dom (dom x + dom y) = dom x + dom y"
  by simp

lemma d_comp_closed [simp]: "dom (dom x \<cdot> dom y) = dom x \<cdot> dom y"
  by simp

lemma d_comm: "dom x \<cdot> dom y = dom y \<cdot> dom x"
  by (smt (verit) add_commute d_absorb_eq d_export d_id local.d_subid local.distl local.distr local.mult_1_left local.mult_1_right local.order_def mult_assoc)

lemma d_demod: "(dom (x \<cdot> y) \<le> dom z) = (x \<cdot> dom y \<le> dom z \<cdot> x)"
proof
  assume h1: "dom (x \<cdot> y) \<le> dom z"
  hence "x \<cdot> dom y = dom (x \<cdot> y) \<cdot> x \<cdot> dom y"
    by (metis d_absorb_eq local.d_local local.dd.mult_assoc)
  also have "\<dots> \<le> dom z \<cdot> x \<cdot> dom y"
    by (simp add: h1 local.mult_isor)
  also have "\<dots> \<le> dom z \<cdot> x"
    using local.d_subid local.mult_isol by fastforce
  finally show "x \<cdot> dom y \<le> dom z \<cdot> x".
next 
  assume h2: "x \<cdot> dom y \<le> dom z \<cdot> x"
  hence "dom (x \<cdot> y) \<le> dom (dom z \<cdot> x)"
    by (metis d_iso local.d_local)
  also have "\<dots> = dom z \<cdot> dom x"
    by simp
  also have "\<dots> \<le> dom z"
    using local.d_subid local.mult_isol by fastforce
  finally show  "dom (x \<cdot> y) \<le> dom z".
qed

lemma lla: "(dom x \<le> dom y) = (x \<le> dom y \<cdot> x)"
  by (metis d_demod d_id local.mult_1_right)

lemma dom_loc_alt: "(x \<cdot> y = 0) = (x \<cdot> dom y = 0)"
  by (metis d_absorb_eq local.annil local.d_local local.d_zero)

lemma dom_mult_distl: "dom x + dom y \<cdot> dom z = (dom x + dom y) \<cdot> (dom x + dom z)"
  by (smt (verit) abel_semigroup.commute d_comm d_idem dadd_closed local.add.abel_semigroup_axioms local.add.semigroup_axioms local.d_subid local.distl local.mult_1_right local.order_def semigroup.assoc)
  
lemma dom_mult_distr: "dom y \<cdot> dom z + dom x = (dom y + dom x) \<cdot> (dom z + dom x)"
  by (simp add: add_commute dom_mult_distl)
 
lemma dom_lb1: "dom x \<cdot> dom y \<le> dom x"
  by (metis d_demod d_id local.d_subid local.mult_1_left)

lemma dom_lb2: "dom x \<cdot> dom y \<le> dom y"
  by (metis d_comm dom_lb1)

lemma dom_glb: "dom z \<le> dom x \<Longrightarrow> dom z \<le> dom y \<Longrightarrow> dom z \<le> dom x \<cdot> dom y"
  by (metis d_idem local.dd.mult_iso)

lemma dom_glb_eq: "(dom z \<le> dom x \<and> dom z \<le> dom y) = (dom z \<le> dom x \<cdot> dom y)"
  using dom_glb dom_lb1 dom_lb2 local.dual_order.trans by blast

definition "fdia x y = dom (x \<cdot> y)"

lemma fdia_demod: "(fdia x y \<le> dom z) = (x \<cdot> dom y \<le> dom z \<cdot> x)"
  by (simp add: d_demod fdia_def)

lemma fdia_act [simp]: "fdia (x \<cdot> y) z = fdia x (fdia y z)"
  by (simp add: fdia_def local.dd.mult_assoc)

lemma fdia_add1 [simp]: "fdia (x + y) z = fdia x z + fdia y z"
  by (simp add: fdia_def local.distr)

lemma fdia_add2 [simp]: "fdia x (y + z) = fdia x y + fdia x z"
  by (simp add: fdia_def local.distl)

lemma fdia_zero1 [simp]: "fdia 0 x = 0"
  by (simp add: fdia_def)

lemma fdia_zero2 [simp]: "fdia x 0 = 0"
  by (simp add: fdia_def)

lemma fdia_one1 [simp]: "fdia 1 x = dom x"
  by (simp add: fdia_def)

lemma fdia_one2 [simp]: "fdia x 1 = dom x"
  by (simp add: fdia_def)

lemma fdia_dom [simp]: "fdia x (dom y) = fdia x y"
  by (simp add: fdia_def)

end


class domain_kleene_algebra = domain_semiring + kleene_algebra

subsection \<open>Codomain semirings\<close>

class codomain_semiring = dioid + cod_op +
  assumes cod_absorb: "x \<le> x \<cdot> cod x" 
  and cod_local: "cod (cod x \<cdot> y) = cod (x \<cdot> y)"
  and cod_add: "cod (x + y) = cod x + cod y"
  and cod_subid: "cod x \<le> 1"
  and cod_zero: "cod 0 = 0"

sublocale codomain_semiring \<subseteq> coddual: domain_semiring  1 "\<lambda>x y. y \<cdot> x" "(+)" 0 "(\<le>)" "(<)" cod
  by (unfold_locales, simp_all add: local.cod_absorb local.cod_local local.cod_add local.cod_subid cod_zero)

abbreviation (in codomain_semiring) "bdia \<equiv> coddual.fdia"

subsection \<open>Modal semirings\<close>

class modal_semiring = domain_semiring + codomain_semiring +
  assumes dc_compat [simp]: "dom (cod x) = cod x" 
  and cd_compat [simp]: "cod (dom x) = dom x" 

sublocale  modal_semiring \<subseteq> msrdual: modal_semiring  1 "\<lambda>x y. y \<cdot> x" "(+)" 0 "(\<le>)" "(<)"  dom cod
  by (unfold_locales, simp_all add: local.d_subid)

lemma (in modal_semiring) d_cod_fix: "(dom x = x) = (x = cod x)"
  by (metis local.cd_compat local.dc_compat)

lemma (in modal_semiring) local_var: "(x \<cdot> y = 0) = (cod x \<cdot> dom y = 0)"
  using local.coddual.dom_loc_alt local.dom_loc_alt by presburger

lemma (in modal_semiring) fbdia_conjugation: "(fdia x (dom p) \<cdot> dom q = 0) = (dom p \<cdot> bdia x (dom q) = 0)"
  by (metis local.cd_compat local.coddual.fdia_def local.d_comm local.dc_compat local.fdia_def local.local_var mult_assoc)

class modal_kleene_algebra = modal_semiring + kleene_algebra

end
