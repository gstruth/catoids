(* 
Title: A Light-Weight Component for Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
with contributions by Peter Höfner
*)

section \<open>Quantales\<close>

theory Quantale_light
  imports Galois_Fusion

begin

text \<open>This is a lightweight component for quantales. It contains some facts that is not in the AFP.
It should eventually be consolidated.\<close>

notation relcomp (infixl ";" 70)

class quantale = complete_lattice + monoid_mult +
  assumes Sup_distl: "x \<cdot> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot> y)" 
  assumes Sup_distr: "\<Squnion>X \<cdot> y = (\<Squnion>x \<in> X. x \<cdot> y)"

interpretation rel_quantale: quantale Inf Sup inf "(\<subseteq>)" "(\<subset>)" sup "{}" "UNIV" Id "(;)"
  by (unfold_locales, auto) 

sublocale quantale \<subseteq> qdual: quantale _ _ _ _ _ _ _ _ _ "\<lambda>x y. y \<cdot> x"
  by (unfold_locales, auto simp: local.Sup_distl mult_assoc local.Sup_distr)

context quantale
begin

lemma sup_Sup: "x \<squnion> y = \<Squnion>{x,y}" 
  by simp

lemma inf_Inf: "x \<sqinter> y = \<Sqinter>{x,y}" 
  by simp

lemma mult_distl: "x \<cdot> (y \<squnion> z) = (x \<cdot> y) \<squnion> (x \<cdot> z)"
  by (smt SUP_empty SUP_insert Sup_distl sup_Sup sup_bot.right_neutral)
 
lemma mult_distr: "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  by (smt SUP_empty SUP_insert Sup_distr sup_Sup sup_bot.right_neutral)

lemma bot_annil [simp]: "\<bottom> \<cdot> x = \<bottom>"
  by (smt (z3) local.SUP_empty local.Sup_distr local.Sup_empty)

lemma bot_annir [simp]: "x \<cdot> \<bottom> = \<bottom>"
  by (smt (z3) local.SUP_empty local.Sup_distl local.Sup_empty)

end

text \<open>Quantales are dioids.\<close>

sublocale quantale \<subseteq> qd: dioid "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)"
  by (unfold_locales, simp_all add: mult_distl mult_distr Sup_distl Sup_distr le_iff_sup less_le SUP_empty sup.assoc, simp add:local.sup.commute)

context quantale
begin

lemma top_top [simp]: "\<top> \<cdot> \<top> = \<top>"
  by (metis (full_types) local.mult_1_right local.sup.commute local.sup_top_left qdual.qd.distr)

text \<open>Composition preserves sups and thus has two right adjoints.\<close>

definition bres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60) where 
  "x \<rightarrow> z = \<Squnion>{y. x \<cdot> y \<le> z}"

definition fres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60) where 
  "z \<leftarrow> y = \<Squnion>{x. x \<cdot> y \<le> z}"

lemma fres_galois: "(x \<cdot> y \<le> z) = (x \<le> z \<leftarrow> y)"
proof 
  show "x \<cdot> y \<le> z \<Longrightarrow> x \<le> z \<leftarrow> y"
    by (simp add: Sup_upper fres_def)
next
  assume "x \<le> z \<leftarrow> y"
  hence "x \<cdot> y \<le> \<Squnion>{x. x \<cdot> y \<le> z} \<cdot> y"
    using fres_def qdual.qd.mult_isol by auto
  also have "... = \<Squnion>{x \<cdot> y |x. x \<cdot> y \<le> z}"
    by (simp add: Sup_distr setcompr_eq_image)
  also have "... \<le> z"
    by (rule Sup_least, auto)
  finally show "x \<cdot> y \<le> z" .
qed

lemma bres_galois: "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"
proof 
  show "x \<cdot> y \<le> z \<Longrightarrow> y \<le> x \<rightarrow> z"
    by (simp add: Sup_upper bres_def)
next
  assume "y \<le> x \<rightarrow> z"
  hence "x \<cdot> y \<le> x \<cdot> \<Squnion>{y. x \<cdot> y \<le> z}"
    using bres_def qdual.qd.mult_isor by force
  also have "... = \<Squnion>{x \<cdot> y |y. x \<cdot> y \<le> z}"
    by (simp add: Sup_distl setcompr_eq_image)
  also have "... \<le> z"
    by (rule Sup_least, safe)
  finally show "x \<cdot> y \<le> z" .
qed 

lemma fres_left_conj:
  "\<Sqinter>X \<leftarrow> y = \<Sqinter>{x \<leftarrow> y |x. x\<in>X}"
  apply (rule order.antisym)
  using fres_galois local.le_Inf_iff apply fastforce
  by (smt (verit, ccfv_threshold) fres_galois local.le_Inf_iff local.order.refl mem_Collect_eq)

lemma Inf_pres_fres: "Inf_pres (\<lambda>x. x \<leftarrow> y)"
  unfolding fun_eq_iff
  apply clarsimp
  oops

lemma fres_top_left: "\<top> \<leftarrow> x = \<top>"
  using fres_galois top_greatest top_unique by blast

lemma fres_canc1: "(y \<leftarrow> x) \<cdot> x \<le> y"
  by (simp add: fres_galois)

lemma fres_canc2: "y \<le> (y \<cdot> x) \<leftarrow> x"
  using fres_galois by force

lemma inf_fres: "y \<cdot> x = \<Sqinter>{z. y \<le> z \<leftarrow> x}"
  by (metis (mono_tags, lifting) fres_canc2 Inf_eqI fres_galois mem_Collect_eq)

lemma bres_iso: "x \<le> y \<Longrightarrow> z \<rightarrow> x \<le> z \<rightarrow> y"
  by (meson bres_galois local.dual_order.trans local.eq_refl)

lemma bres_anti: "x \<le> y \<Longrightarrow> y \<rightarrow> z \<le> x \<rightarrow> z"
  by (smt Sup_le_iff bres_def bres_galois fres_galois order_trans mem_Collect_eq)

lemma fres_iso: "x \<le> y \<Longrightarrow> x \<leftarrow> z \<le> y \<leftarrow> z"
  using fres_galois dual_order.trans by blast

lemma bres_top_top [simp]: "\<top> \<rightarrow> \<top> = \<top>"
  by (meson bres_galois local.dual_order.eq_iff local.top_greatest)

lemma fres_top_top [simp]: "\<top> \<leftarrow> \<top> = \<top>"
  using fres_galois top_greatest top_le by blast

lemma bres_bot_bot [simp]: "\<bottom> \<rightarrow> \<bottom> = \<top>"
  by (simp add: bres_def)

lemma left_sided_localp: "\<top> \<cdot> y = y \<Longrightarrow> x \<cdot> y \<le> y"
  by (metis local.top_greatest qdual.qd.mult_isol)

lemma fres_sol: "((y \<leftarrow> x) \<cdot> x = y) = (\<exists>z. z \<cdot> x = y)"
  using fres_canc1 fres_canc2 local.antisym_conv qdual.qd.mult_isol by blast

lemma sol_fres: "((y \<cdot> x) \<leftarrow> x = y) = (\<exists>z. y = z \<leftarrow> x)"
  by (metis fres_canc1 fres_canc2 fres_iso local.antisym_conv)

lemma fres_zero_canc [simp]: "(\<bottom> \<leftarrow> y) \<cdot> y = \<bottom>"
  using fres_canc1 le_bot by blast

lemma fres_top_canc [simp]: "(\<top> \<cdot> x) \<leftarrow> x = \<top>"
  by (simp add: fres_canc2 top_le)

lemma fres_canc3 [simp]: "((x \<cdot> y) \<leftarrow> y) \<cdot> y = x \<cdot> y"
  using fres_sol by blast

lemma fres_canc4 [simp]: "((x \<leftarrow> y) \<cdot> y) \<leftarrow> y = x \<leftarrow> y"
  using sol_fres by blast

lemma fres_anti: "x \<le> y \<Longrightarrow> z \<leftarrow> y \<le> z \<leftarrow> x"
  by (meson bres_galois fres_canc1 fres_galois local.dual_order.trans)

lemma bres_canc1: "x \<cdot> (x \<rightarrow> y) \<le> y"
  by (simp add: bres_galois)

lemma bres_canc2: "y \<le> x \<rightarrow> (x \<cdot> y)"
  using bres_galois by auto

lemma inf_bres: "x \<cdot> y = \<Sqinter>{z. y \<le> x \<rightarrow> z}"
  using bres_galois fres_galois inf_fres by force

lemma bres_sol: "(x \<cdot> (x \<rightarrow> y) = y) = (\<exists>z. x \<cdot> z = y)"
  using bres_canc1 bres_canc2 local.antisym_conv qdual.qd.mult_isor by blast

lemma sol_bres: "(x \<rightarrow> (x \<cdot> y) = y) = (\<exists>z. y = x \<rightarrow> z)"
  by (metis bres_canc1 bres_canc2 bres_iso local.antisym_conv)

lemma bres_right_conj: "y \<rightarrow> \<Sqinter>X = \<Sqinter>{y \<rightarrow> x |x. x \<in> X}"
  apply (rule order.antisym)
  using bres_iso local.Inf_lower local.le_Inf_iff apply auto[1]
  by (smt (verit, ccfv_threshold) bres_galois local.le_Inf_iff local.order_refl mem_Collect_eq)

lemma bres_right_conj': "z \<rightarrow> (x \<sqinter> y) = (z \<rightarrow> x) \<sqinter> (z \<rightarrow> y)"
  apply (rule order.antisym)
   apply (simp add: bres_iso)
  using bres_galois inf_le1 inf_le2 le_inf_iff by blast

lemma fres_right_antidisj: "x \<leftarrow> \<Squnion>Y = (\<Sqinter>y \<in> Y. x \<leftarrow> y)"
  apply (rule order.antisym)
  apply (simp add: fres_anti local.INF_greatest local.Sup_upper)
  by (smt (verit, ccfv_threshold) fres_galois local.SUP_le_iff local.Sup_distl local.le_INF_iff local.order.refl)

lemma fres_right_antidisj': "x \<leftarrow> (y \<squnion> z) = (x \<leftarrow> y) \<sqinter> (x \<leftarrow> z)"
  apply (rule order.antisym)
   apply (simp add: fres_anti bres_galois)
  using bres_galois fres_galois by fastforce

lemma bres_left_antidisj: "\<Squnion>Y \<rightarrow> x = (\<Sqinter>y \<in> Y. y \<rightarrow> x)"
  apply (rule order.antisym)
  apply (simp add: bres_anti local.INF_greatest local.Sup_upper)
  by (smt (verit, ccfv_threshold) bres_galois fres_galois local.Sup_least local.le_INF_iff local.order_refl)

lemma bres_left_antidisj': "(x \<squnion> y) \<rightarrow> z = (x \<rightarrow> z) \<sqinter> (y \<rightarrow> z)"
  apply (rule order.antisym)
  apply (simp add: bres_anti)
  by (meson bres_galois fres_galois local.inf_le1 local.inf_le2 local.sup.bounded_iff)

lemma bres_top_right [simp]: "x \<rightarrow> \<top> = \<top>"
  using bres_galois top_greatest top_unique by blast

lemma fres_right_bot [simp]: "x \<leftarrow> \<bottom> = \<top>"
  using fres_galois top_unique by fastforce

lemma bres_left_bot [simp]: "\<bottom> \<rightarrow> x = \<top>"
  using bres_galois top_unique by fastforce

lemma bres_zero_canc [simp]: "y \<cdot> (y \<rightarrow> \<bottom>) = \<bottom>"
  using bres_canc1 le_bot by blast

lemma bres_top_canc [simp]: "x \<rightarrow> (x \<cdot> \<top>) = \<top>"
  by (simp add: bres_canc2 top_le)

lemma bres_canc3 [simp]: "x \<cdot> (x \<rightarrow> (x \<cdot> y)) = x \<cdot> y"
  using bres_sol by blast

lemma bres_canc4 [simp]: "x \<rightarrow> (x \<cdot> (x \<rightarrow> y)) = x \<rightarrow> y"
  using sol_bres by blast

lemma bres_fres_canc: "x \<le> y \<leftarrow> (x \<rightarrow> y)"
  using bres_canc1 fres_galois by simp

lemma bres_fres_iso: "x \<le> y \<Longrightarrow> z \<leftarrow> (x \<rightarrow> z) \<le> z \<leftarrow> (y \<rightarrow> z)"
  by (simp add: bres_anti fres_anti) 

lemma double_fres_bres_canc [simp]: "z \<leftarrow> ((z \<leftarrow> (x \<rightarrow> z)) \<rightarrow> z) = z \<leftarrow> (x \<rightarrow> z)"
  using bres_canc1 bres_galois dual_order.antisym fres_anti fres_galois by fastforce

lemma fres_curry: "(z \<leftarrow> y) \<leftarrow> x = z \<leftarrow> (x \<cdot> y)"
  by (metis fres_canc1 fres_galois order.antisym mult_assoc)

lemma le_top: "x \<le> \<top> \<cdot> x"
  by (metis local.mult_1_left local.top_greatest qdual.qd.mult_isol)

lemma bres_one: "1 \<le> x \<rightarrow> x"
  using bres_galois by force

lemma fres_one: "1 \<le> x \<leftarrow> x"
  using fres_galois by fastforce

lemma fres_xxx [simp]: "(x \<leftarrow> x) \<cdot> x = x"
  using fres_sol mult_1_left by blast

lemma fres_one_right [simp]: "x \<leftarrow> 1 = x"
  by (metis fres_sol mult_1_right)

lemma fres_1_left: "1 \<leftarrow> x \<le> y \<leftarrow> (x \<cdot> y)"
  using fres_one fres_curry fres_iso by fastforce

lemma fres_interchange: "z \<cdot> (x \<leftarrow> y) \<le> (z \<cdot> x) \<leftarrow> y"
  by (metis fres_canc1 fres_galois mult_assoc qdual.qd.mult_isor)

lemma fres_trans: "(x \<leftarrow> y) \<cdot> (y \<leftarrow> z) \<le> x \<leftarrow> z"
  using dual_order.trans fres_galois fres_interchange by blast

lemma fres_canc5: "x \<leftarrow> y \<le> (x \<leftarrow> z) \<leftarrow> (y \<leftarrow> z)"
  by (simp add: fres_anti fres_canc1 fres_curry)

lemma Inf_subdistl: "x \<cdot> \<Sqinter>Y \<le> (\<Sqinter>y \<in> Y. x \<cdot> y)"
  by (simp add: local.Inf_lower local.le_INF_iff qdual.qd.mult_isor)

lemma Inf_subdistr: "\<Sqinter> X \<cdot> y \<le> (\<Sqinter>x \<in> X. x \<cdot> y)"
  by (simp add: local.INF_greatest local.Inf_lower qdual.qd.mult_iso)

lemma bres_interchange: "(x \<rightarrow> y) \<cdot> z \<le> x \<rightarrow> (y \<cdot> z)"
  by (metis bres_canc1 bres_galois mult_assoc qdual.qd.mult_isol)

lemma bres_curry: "x \<rightarrow> (y \<rightarrow> z) = (y \<cdot> x) \<rightarrow> z"
  by (metis bres_canc1 bres_galois dual_order.antisym mult_assoc)

lemma fres_bres: "x \<rightarrow> (y \<leftarrow> z) = (x \<rightarrow> y) \<leftarrow> z"
  apply (rule order.antisym)
  apply (metis bres_fres_canc bres_galois fres_curry fres_galois)
  using bres_fres_canc bres_galois fres_canc5 fres_galois local.dual_order.trans by blast

lemma bres_trans: "(x \<rightarrow> y) \<cdot> (y \<rightarrow> z) \<le> x \<rightarrow> z"
  using dual_order.trans bres_galois bres_interchange by blast

lemma bres_canc5: "x \<rightarrow> y \<le> (z \<rightarrow> x) \<rightarrow> (z \<rightarrow> y)"
  by (simp add: bres_anti bres_canc1 bres_curry)

lemma bres_xxx [simp]: "x \<cdot> (x \<rightarrow> x) = x"
  using bres_sol mult_1_right by fastforce

lemma bres_one_left [simp]: "1 \<rightarrow> x = x"
  by (metis bres_sol mult_1_left)

lemma bres_1_right: "x \<rightarrow> 1 \<le> (y \<cdot> x) \<rightarrow> y"
  using bres_one bres_curry bres_iso by fastforce

lemma bres_fres_one_eq: "x \<leftarrow> (1 \<rightarrow> x) = x \<leftarrow> x"
  by simp

text \<open>A Kleene star can be defined in any quantale.\<close>

definition "qstar x = \<Squnion>{x ^ i |i. i \<ge> 0}"

lemma qstar_distl: "x \<cdot> (qstar y) = \<Squnion>{(x \<cdot> y ^ i)|i. i \<ge> 0}"
  apply (rule order.antisym)
  apply (smt (verit, ccfv_SIG) local.SUP_le_iff local.Sup_distl local.Sup_upper mem_Collect_eq qstar_def)
  by (smt (verit, ccfv_SIG) local.SUP_upper2 local.Sup_distl local.Sup_least local.order_refl mem_Collect_eq qstar_def)

lemma qstar_distr: "(qstar x) \<cdot> y = \<Squnion>{x ^ i \<cdot> y|i. i \<ge> 0}"
  apply (rule order.antisym)
   apply (smt (verit, ccfv_threshold) local.SUP_le_iff local.Sup_distr local.Sup_upper mem_Collect_eq qstar_def)
  by (smt (verit, del_insts) local.Sup_least local.Sup_upper mem_Collect_eq qdual.qd.mult_isol qstar_def)

lemma star_unfold_aux: "x ^ 0 \<squnion> \<Squnion>{x ^ i |i. i \<ge> 1} = \<Squnion>{x ^ i |i. i \<ge> 0}"
  apply (rule order.antisym)
   apply (intro sup_least Sup_least, simp_all)
  apply (metis (mono_tags, lifting) local.Sup_upper local.power.power_0 mem_Collect_eq)
  apply (metis (mono_tags, lifting) local.Sup_upper mem_Collect_eq)
  apply (rule Sup_least, simp)
  by (metis (mono_tags, lifting) insertCI le_zero_eq local.Sup_insert local.Sup_upper local.power_eq_if mem_Collect_eq not_less_eq_eq)

lemma star_unfoldl: "1 \<squnion> x \<cdot> qstar x = qstar x"
proof-
  have "1 \<squnion> x \<cdot> qstar x = x ^ 0 \<squnion> \<Squnion>{x \<cdot> x ^ i |i. i \<ge> 0}"
    using qstar_distl by fastforce
  also have "\<dots> =  x ^ 0 \<squnion> \<Squnion>{x ^ i |i. i \<ge> 1}"
    by (smt (verit, best) Collect_cong le0 le_add_same_cancel1 le_zero_eq local.power.power_Suc local.power_Suc2 local.power_eq_if local.power_one_right plus_1_eq_Suc)
  finally show ?thesis
    using qstar_def star_unfold_aux by auto
qed

lemma star_unfoldr: "1 \<squnion> qstar x \<cdot> x = qstar x"
proof-
  have "1 \<squnion> qstar x \<cdot> x = x ^ 0 \<squnion> \<Squnion>{x ^ i \<cdot> x |i. i \<ge> 0}"
    by (simp add: qstar_distr)
  also have "\<dots> =  x ^ 0 \<squnion> \<Squnion>{x ^ i |i. i \<ge> 1}"
    by (smt (verit, best) Collect_cong le0 le_add_same_cancel1 le_zero_eq local.power.power_Suc local.power_Suc2 local.power_eq_if local.power_one_right plus_1_eq_Suc)
  finally show ?thesis
    using qstar_def star_unfold_aux by auto
qed

lemma star_inductl: "z \<squnion> x \<cdot> y \<le> y \<Longrightarrow> qstar x \<cdot> z \<le> y"
  unfolding qstar_distr
  using local.Sup_le_iff qdual.qd.dd.power_inductl by force 

lemma star_inductr: "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> qstar x \<le> y"
  unfolding qstar_distl
  using local.Sup_le_iff qdual.qd.dd.power_inductr by force

end

text \<open>Every quantale is thus a Kleene algebra.\<close>

sublocale quantale \<subseteq> qk: kleene_algebra "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>"  "(\<le>)" "(<)" qstar
  by unfold_locales (simp_all add: star_unfoldl star_unfoldr star_inductl star_inductr)

class commutative_quantale = quantale + ab_semigroup_mult

class distributive_quantale = quantale + distrib_lattice

class boolean_quantale = quantale + boolean_algebra

end
