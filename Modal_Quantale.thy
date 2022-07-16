(* 
Title: Modal Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Modal Quantales\<close>

theory Modal_Quantale
  imports Quantale_light MKA_light

begin

class domain_quantale = quantale + dom_op +
  assumes dom_absorb: "x \<le> dom x \<cdot> x"
  and dom_local: "dom (x \<cdot> dom y) = dom (x \<cdot> y)"
  and dom_add: "dom (x \<squnion> y) = dom x \<squnion> dom y"
  and dom_subid: "dom x \<le> 1"
  and dom_zero [simp]: "dom \<bottom> = \<bottom>"

text \<open>The definition is that of a domain semigroup. The following sublocale statement brings all
those properties into scope.\<close>

sublocale domain_quantale \<subseteq> dqmka: domain_kleene_algebra "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar dom
  by (unfold_locales, simp_all add: local.dom_absorb local.dom_local local.dom_add local.dom_subid)

context domain_quantale
begin

lemma dom_top [simp]: "dom \<top> = 1"
proof-
  have "1 \<le> \<top>"
    by simp
  hence "dom 1 \<le> dom \<top>"
    using local.dqmka.d_iso by blast
  thus ?thesis
    by (simp add: local.dom_subid local.dual_order.antisym)
qed

lemma dom_top2: "x \<cdot> \<top> \<le> dom x \<cdot> \<top>"
proof-
  have "x \<cdot> \<top> = dom x \<cdot> x \<cdot> \<top>"
    by simp
  also have "\<dots> \<le> dom x \<cdot> \<top> \<cdot> \<top>"
    using local.order_refl local.top_greatest qdual.qd.mult_iso by presburger
  finally show ?thesis
    by (simp add: local.mult.semigroup_axioms semigroup.assoc)
qed

lemma weak_twisted: "x \<cdot> dom y \<le> dom (x \<cdot> y) \<cdot> x"
  using local.dqmka.d_demod by blast

lemma dom_meet: "dom x \<cdot> dom y = dom x \<sqinter> dom y"
  apply (rule order.antisym)
  apply (simp add: local.dqmka.dom_lb1 local.dqmka.dom_lb2)
  by (metis local.dqmka.d_absorb_eq local.dqmka.d_invol local.dqmka.d_iso local.inf.cobounded1 local.inf.cobounded2 qdual.qd.mult_iso)

lemma dom_meet_pres: "dom (dom x \<sqinter> dom y) = dom x \<sqinter> dom y"
  using dom_meet local.dqmka.d_comp_closed by fastforce

lemma dom_meet_distl: "dom x \<cdot> (y \<sqinter> z) = (dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)"
proof-
  have a: "dom x \<cdot> (y \<sqinter> z) \<le> (dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)"
    by (simp add: qdual.qd.mult_isor)
  have "(dom x \<cdot> y) \<sqinter> (dom x \<cdot> z) = dom ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)) \<cdot> ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z))"
    by simp
  also have "\<dots> \<le> dom ((dom x \<cdot> y)) \<cdot> ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z))"
    using local.dqmka.d_iso local.inf_le1 qdual.qd.mult_isol by blast
  also have "\<dots> \<le> dom x \<cdot> ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z))"
    by (simp add: dom_meet local.dqmka.d_demod qdual.qd.dd.mult_iso)
  also have "\<dots> \<le> dom x \<cdot> (y \<sqinter> z)"
    by (metis local.dom_subid local.inf_mono local.mult_1_left qdual.qd.mult_isol qdual.qd.mult_isor)
  finally show ?thesis
    using a local.dual_order.antisym by blast
qed

lemma dom_meet_approx: "dom ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)) \<le> dom x"
  by (simp add: dom_meet_distl local.dqmka.lla local.qdual.mult_assoc)

lemma dom_inf_pres_aux: "Y \<noteq> {} \<Longrightarrow> dom (\<Sqinter>{dom x \<cdot> y |y. y\<in>Y}) \<le> dom x"
proof-
  assume "Y \<noteq> {}"
  have "\<forall>z\<in>Y. dom (\<Sqinter>{dom x \<cdot> y |y. y\<in>Y}) \<le> dom (dom x \<cdot> z)"
    by (metis (mono_tags, lifting) local.Inf_lower local.dqmka.d_iso mem_Collect_eq)
  hence "\<forall>z\<in>Y. dom (\<Sqinter>{dom x \<cdot> y |y. y\<in>Y}) \<le> dom x \<cdot> dom z"
    using local.dqmka.d_export by fastforce
  hence "\<forall>z\<in>Y. dom (\<Sqinter>{dom x \<cdot> y |y. y\<in>Y}) \<le> dom x"
    using dom_meet by fastforce
  thus "dom (\<Sqinter>{dom x \<cdot> y |y. y\<in>Y}) \<le> dom x"
    using \<open>Y \<noteq> {}\<close> by blast
qed

lemma dom_inf_pres_aux2: "\<Sqinter>{dom x \<cdot> y |y. y\<in>Y} \<le> \<Sqinter>Y"
  by (smt (z3) local.Inf_mono local.dqmka.d_absorb_eq local.dqmka.d_comm local.dqmka.d_export local.dqmka.lla local.order.eq_iff mem_Collect_eq mult_assoc qdual.qd.mult_isol)

lemma dom_inf_pres: "Y \<noteq> {} \<Longrightarrow> dom x \<cdot> (\<Sqinter>Y) = \<Sqinter>{dom x \<cdot> y |y. y\<in>Y}"
proof-
  assume hyp: "Y \<noteq> {}"
  have a: "dom x \<cdot> (\<Sqinter>Y) \<le> \<Sqinter>{dom x \<cdot> y |y. y\<in>Y}"
    by (simp add: Setcompr_eq_image local.Inf_subdistl)
  have "\<Sqinter>{dom x \<cdot> y |y. y\<in>Y} = dom (\<Sqinter>{dom x \<cdot> y |y. y\<in>Y}) \<cdot> \<Sqinter>{dom x \<cdot> y |y. y\<in>Y}"
    by simp
  also have "\<dots> \<le> dom x \<cdot> \<Sqinter>{dom x \<cdot> y |y. y\<in>Y}"
    using dom_inf_pres_aux hyp local.dqmka.lla by force
  also have "\<dots> \<le> dom x \<cdot> \<Sqinter>Y"
    by (simp add: dom_inf_pres_aux2 qdual.qd.mult_isor)
  finally show ?thesis
    using a order.antisym by blast
qed

lemma "x \<cdot> (\<Sqinter>Y) \<le> \<Sqinter>{x \<cdot> y |y. y\<in>Y}"
  by (simp add: Setcompr_eq_image local.Inf_subdistl)

lemma "(\<Sqinter>X) \<cdot> y \<le> \<Sqinter>{x \<cdot> y |x. x\<in>X}"
  by (simp add: Setcompr_eq_image local.Inf_subdistr)

lemma "dom (\<Sqinter>X) \<le> \<Sqinter>{dom x|x. x\<in>X}"
  by (simp add: Setcompr_eq_image local.INF_greatest local.Inf_lower local.dqmka.d_iso)

lemma dom_top_pres: "(x \<le> dom y \<cdot> x) = (x \<le> dom y \<cdot> \<top>)"
  by (smt (verit) local.dqmka.d_export local.dqmka.d_iso local.dqmka.dom_glb_eq local.dqmka.lla local.order.trans local.top_greatest qdual.qd.mult_iso)

lemma dom_lla_var: "(dom x \<le> dom y) = (x \<le> dom y \<cdot> \<top>)"
  using dom_top_pres local.dqmka.lla by presburger

lemma "dom (1 \<sqinter> x) = 1 \<sqinter> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> dom x = x"
  using local.inf_absorb2 by auto

lemma dom_meet_sub: "dom (x \<sqinter> y) \<le> dom x \<sqinter> dom y"
  by (simp add: local.dqmka.d_iso)

lemma dom_top: "dom x \<cdot> \<top> = x \<cdot> \<top>"
  nitpick (* counterexample *)
  oops

definition "fd x y = dom (x \<cdot> y)"

lemma fd_fdia [simp]: "fd x y = dqmka.fdia x y"
  by (simp add: fd_def local.dqmka.fdia_def)

definition "bb x y = \<Squnion>{dom z |z. fd x z \<le> dom y}"

lemma bb_demod: "(dom y \<le> bb x z) = (x \<cdot> dom y \<le> dom z \<cdot> x)"
  oops

lemma  fdbb_galois: 
  assumes "dom p = p" and "dom q = q"
  shows "(fd x p \<le> q) = (p \<le> bb x q)"
proof
  assume "fd x p \<le> q"
  hence "p \<in> {dom z |z. fd x z \<le> dom q}"
    using assms(1) assms(2) by force
  hence "p \<le> \<Squnion>{dom z |z. fd x z \<le> dom q}"
    using local.Sup_upper by presburger
  thus "p \<le> bb x q"
    using bb_def by force
next 
  assume "p \<le> bb x q"
  hence "p \<le> \<Squnion>{dom z |z. fd x z \<le> dom q}"
    by (simp add: bb_def)
  hence "fd x p \<le> fd x (\<Squnion>{dom z |z. fd x z \<le> dom q})"
    by (simp add: local.dqmka.d_iso local.dqmka.fdia_def qdual.qd.mult_isor)
  also have "\<dots> = dom (x \<cdot> \<Squnion>{dom z |z. fd x z \<le> dom q})"
   sorry
  also have "\<dots> = \<Squnion>{dom (x \<cdot> dom z) |z. fd x z \<le> dom q}"
    sorry  (*this is something we can't prove with Isabelle *)
  also have "\<dots> = \<Squnion>{fd x z |z. fd x z \<le> dom q}"
    using fd_def local.dom_local by force
  also have "\<dots> \<le> dom q"
    by (smt (verit) local.Sup_least mem_Collect_eq)
  finally show "fd x p \<le> q"
    using assms(2) by force
qed

end

class codomain_quantale = quantale + cod_op +
  assumes cod_absorb: "x \<le> x \<cdot> cod x" 
  and cod_local: "cod (cod x \<cdot> y) = cod (x \<cdot> y)"
  and cod_add: "cod (x \<squnion> y) = cod x \<squnion> cod y"
  and cod_subid: "cod x \<le> 1"
  and cod_zero: "cod \<bottom> = \<bottom>"

sublocale codomain_quantale \<subseteq> coddual: domain_quantale cod _ _ _ _ _ _ _ _ _ "\<lambda>x y. y \<cdot> x"
  by (unfold_locales, simp_all add: local.cod_absorb local.cod_local local.cod_add local.cod_subid cod_zero)

abbreviation (in codomain_quantale) "bd \<equiv> coddual.fd"

definition  (in codomain_quantale) "fb x y = \<Squnion>{dom z |z. bd x (dom z) \<le> dom y}"

class modal_quantale = domain_quantale + codomain_quantale +
  assumes dc_compat [simp]: "dom (cod x) = cod x" 
  and cd_compat [simp]: "cod (dom x) = dom x" 

lemma (in modal_quantale)  "dom x \<cdot> \<top> = x \<cdot> \<top>"
  nitpick (* counterexample *)
  oops

sublocale modal_quantale \<subseteq> mqs: modal_kleene_algebra "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" "qstar" "cod" "dom"
  by (unfold_locales, simp_all add: local.cod_absorb local.cod_local local.cod_add local.cod_subid)

sublocale modal_quantale \<subseteq> mqdual: modal_quantale  "dom" _ _ _ _ _ _ _ _ _ "\<lambda>x y. y \<cdot> x" "cod"
  by (unfold_locales, simp_all add: local.dom_local local.dom_add local.dom_subid local.cod_local local.cod_add local.cod_subid)

end



