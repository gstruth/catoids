(* 
Title: Quantales with Converse
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Quantales with Converse\<close>

theory Quantale_conv
  imports Modal_Quantale MKA_conv

begin

subsection \<open>Involutive quantales\<close>

text \<open>The following axioms for involutive quantales are standard.\<close>

class involutive_quantale = quantale + invol_op +
  assumes inv_invol: "(x\<^sup>\<circ>)\<^sup>\<circ> = x"
  and inv_contrav: "(x \<cdot> y)\<^sup>\<circ> = y\<^sup>\<circ> \<cdot> x\<^sup>\<circ>"
  and inv_sup: "(\<Squnion>X)\<^sup>\<circ> = \<Squnion>{x\<^sup>\<circ> |x. x \<in> X}"

context involutive_quantale
begin

lemma inv_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<circ> \<le> y\<^sup>\<circ>"
  by (smt (verit, ccfv_SIG) insertI1 insertI2 local.Sup_upper local.inv_sup local.sup.absorb1 local.sup_Sup mem_Collect_eq)

lemma inv_binsup: "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> \<squnion> y\<^sup>\<circ>"
  apply (rule order.antisym)
   apply (metis local.inv_invol local.inv_iso local.sup.cobounded1 local.sup.cobounded2 qdual.qd.add_least)
  by (simp add: local.inv_iso)

end

sublocale involutive_quantale \<subseteq> invqka: involutive_kleene_algebra invol "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar
  by (unfold_locales, simp_all add: local.inv_contrav inv_binsup inv_invol)

context involutive_quantale
begin

lemma inv_binf [simp]: "(x \<sqinter> y)\<^sup>\<circ> = x\<^sup>\<circ> \<sqinter> y\<^sup>\<circ>"
proof-
  {fix z
  have "(z \<le> (x \<sqinter> y)\<^sup>\<circ>) = (z\<^sup>\<circ> \<le> x \<sqinter> y)"
    using invqka.inv_adj by blast
  also have "\<dots> = (z\<^sup>\<circ> \<le> x \<and> z\<^sup>\<circ> \<le> y)"
    by simp
  also have "\<dots> = (z \<le> x\<^sup>\<circ> \<and> z \<le> y\<^sup>\<circ>)"
    by (simp add: invqka.inv_adj)
  also have "\<dots> = (z \<le> x\<^sup>\<circ> \<sqinter> y\<^sup>\<circ>)"
    by simp
  finally have "(z \<le> (x \<sqinter> y)\<^sup>\<circ>) = (z \<le> x\<^sup>\<circ> \<sqinter> y\<^sup>\<circ>)".}
  thus ?thesis
    using local.dual_order.antisym by blast
qed

lemma inv_inf [simp]: "(\<Sqinter>X)\<^sup>\<circ> = \<Sqinter>{x\<^sup>\<circ> |x. x \<in> X}"
  apply (rule order.antisym)
  using invqka.inv_adj local.Inf_lower local.le_Inf_iff apply auto[1]
  by (metis (mono_tags, lifting) invqka.inv_adj local.Inf_greatest local.Inf_lower mem_Collect_eq)

lemma inv_top [simp]: "\<top>\<^sup>\<circ> = \<top>"
proof-
  have a: "\<top>\<^sup>\<circ> \<le> \<top>"
    by simp
  hence "(\<top>\<^sup>\<circ>)\<^sup>\<circ> \<le> \<top>\<^sup>\<circ>"
    using local.inv_iso by blast
  hence "\<top> \<le> \<top>\<^sup>\<circ>"
    by simp
  thus ?thesis
    by (simp add: local.top_le)
qed
lemma inv_qstar_aux [simp]: "(x^i)\<^sup>\<circ> = (x\<^sup>\<circ>) ^ i"
  apply (induct i)
  using local.inv_contrav local.power_Suc2 by auto

lemma inv_conjugate: "(x\<^sup>\<circ> \<sqinter> y = \<bottom>) = (x \<sqinter> y\<^sup>\<circ> = \<bottom>)"
  using inv_binf invqka.inv_zero by fastforce

definition "do x = 1 \<sqinter> (x \<cdot> x\<^sup>\<circ>)"

definition "cd x = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> x)"

lemma do_inv: "do (x\<^sup>\<circ>) = cd x"
proof-
  have "do (x\<^sup>\<circ>) = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> (x\<^sup>\<circ>)\<^sup>\<circ>)"
    by (simp add: do_def)
  also have "\<dots> = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> x)"
    by simp
  also have "\<dots> = cd x"
    by (simp add: cd_def)
  finally show ?thesis.
qed

lemma cd_inv: "cd (x\<^sup>\<circ>) = do x"
  by (simp add: cd_def do_def)

lemma do_le_top: "do x \<le> 1 \<sqinter> (x \<cdot> \<top>)"
  using do_def local.inf_mono local.order_refl local.top_greatest qdual.qd.mult_iso by presburger

lemma do_subid: "do x \<le> 1"
  by (simp add: do_def)

lemma do_bot [simp]: "do \<bottom> = \<bottom>"
  by (simp add: do_def)

lemma do_iso: "x \<le> y \<Longrightarrow> do x \<le> do y"
  using do_def local.eq_refl local.inf_mono local.inv_iso qdual.qd.dd.mult_iso by presburger

lemma do_subdist: "do x \<squnion> do y \<le> do (x \<squnion> y)"
proof-
  have "do x \<le> do (x \<squnion> y)" and  "do y \<le> do (x \<squnion> y)"
    by (simp_all add: do_iso)
  thus ?thesis
    by simp
qed

lemma inv_do [simp]: "(do x)\<^sup>\<circ> = do x"
  by (simp add: do_def)

lemma inv_cd [simp]: "(cd x)\<^sup>\<circ> = cd x"
  by (metis do_inv inv_do)

text \<open>The strong Gelfand property (name by Palmigiano and Re) is important for dioids and Kleene algebras.\<close>

lemma strong_gelfand: "x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"
  nitpick (* counterexample *)
  oops

  text \<open>The modular law is a convenient axiom for relational quantales, in a setting where the underlying
lattice is not boolean.\<close>

lemma modular_law: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  nitpick (* counterexample *)
  oops

lemma dedekind: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  nitpick (* counterexample *)
  oops

end


sublocale commutative_quantale \<subseteq> ciq: involutive_quantale id _ _ _ _ _ _ _ _ _ _ 
  by (unfold_locales, simp_all add: mult_commute)


class distributive_involutive_quantale = involutive_quantale + distributive_quantale

class boolean_involutive_quantale = involutive_quantale + boolean_quantale

class quantale_converse = involutive_quantale +
  assumes strong_gelfand: "x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"

begin

lemma modular_law: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  nitpick (* counterexample *)
  oops

lemma peirce_1: "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom> \<Longrightarrow> (y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
  nitpick (* counterexample *)
  oops

lemma dedekind: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  nitpick (* counterexample *)
  oops

lemma do_gelfand [simp]: "do x \<cdot> do x \<cdot> do x = do x"
  apply (rule order.antisym)
   apply (metis local.do_def local.inf.cobounded1 local.mult_1_right qdual.qd.mult_iso qdual.qd.mult_isor)
  by (metis local.inv_do local.strong_gelfand)

lemma cd_gelfand [simp]: "cd x \<cdot> cd x \<cdot> cd x = cd x"
  by (metis do_gelfand local.do_inv)

lemma do_idem [simp]: "do x \<cdot> do x  = do x"
proof (rule order.antisym)
  show a: "do x \<cdot> do x \<le> do x"
    using local.do_subid qdual.qd.mult_isor by fastforce
  have "do x = do x \<cdot> do x \<cdot> do x"
    by simp
  thus "do x \<le> do x \<cdot> do x"
    by (metis a qdual.qd.mult_isol)
qed

lemma cd_idem: "cd x \<cdot> cd x  = cd x"
  by (metis do_idem local.do_inv)

lemma dodo [simp]: "do (do x) = do x"
proof-
  have "do (do x) = 1 \<sqinter> (do x \<cdot> do x)"
    using local.do_def local.inv_do by force
  also have "\<dots> = 1 \<sqinter> do x"
    by simp
  also have "\<dots> = do x"
    by (simp add: local.do_def)
  finally show ?thesis.
qed

lemma cdcd: "cd (cd x) = cd x"
  using cd_idem local.cd_def local.inv_cd by force

lemma docd_compat [simp]: "do (cd x) = cd x"
proof-
  have "do (cd x) = do (do (x\<^sup>\<circ>))"
    by (simp add: local.do_inv)
  also have "\<dots> = do (x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cd x"
    by (simp add: local.do_inv)
  finally show ?thesis.
qed

lemma cddo_compat [simp]: "cd (do x) = do x"
  by (metis docd_compat local.cd_inv local.inv_do)

lemma "do x = 1 \<sqinter> (x \<cdot> \<top>)"
  nitpick
  oops
 
end

sublocale quantale_converse \<subseteq> convqka: kleene_algebra_converse invol "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)"  qstar
  by (unfold_locales, simp add: local.strong_gelfand)

class dedekind_quantale = involutive_quantale +
  assumes modular_law: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"


subsection \<open>Dedekind quantales\<close>

sublocale dedekind_quantale \<subseteq> convdqka: kleene_algebra_converse invol "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar
  by (unfold_locales, metis local.inf.absorb2 local.le_top local.modular_law local.top_greatest)

context dedekind_quantale
begin

subclass quantale_converse
  apply unfold_locales
  by (simp add: local.convdqka.strong_gelfand)

lemma modular_2 [simp]: "((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<sqinter> z = (x \<cdot> y) \<sqinter> z"

  by (meson local.inf.cobounded1 local.inf_le2 local.inf_mono local.le_infI local.modular_law local.order_eq_iff qdual.qd.mult_iso)

lemma modular_1 [simp]: "(x \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))) \<sqinter> z = (x \<cdot> y) \<sqinter> z"
  by (metis local.inv_binf local.inv_contrav local.inv_invol modular_2)

lemma dedekind: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  by (smt (verit, ccfv_threshold) local.inf_commute local.inv_binf local.inv_contrav local.inv_invol local.modular_law modular_1)

lemma modular3: "(x \<cdot> y) \<sqinter> z \<le> x \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  by (metis local.inf.cobounded1 modular_1)

lemma peirce: "((x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>) = ((y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>)"
  by (metis local.bot_annil local.inf.commute local.inf_bot_right local.inv_conjugate local.inv_contrav modular_2)

lemma schroeder_1: "((x \<cdot> y) \<sqinter> z = \<bottom>) = (y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>)"
  by (metis local.inf.commute local.inv_conjugate local.inv_contrav local.inv_invol peirce) 

lemma schroeder_2: "((x \<cdot> y) \<sqinter> z = \<bottom>) = (x \<sqinter> (z \<cdot> y\<^sup>\<circ>) = \<bottom>)"
  by (metis local.bot_annil local.bot_unique local.inf.commute local.inv_invol local.modular_law)

lemma lla_top_aux: "p \<le> 1 \<Longrightarrow> ((x \<le> p \<cdot> x) = (x \<le> p \<cdot> \<top>))"
proof
  assume h: "p \<le> 1"
  and h1: "x \<le> p \<cdot> x"
  thus "x \<le> p \<cdot> \<top>"
    using local.order_trans local.top_greatest qdual.qd.mult_isor by blast
next 
  assume h: "p \<le> 1"
  and "x \<le> p \<cdot> \<top>"
  hence "x = (p \<cdot> \<top>) \<sqinter> x"
    using local.inf.absorb_iff2 by auto
  also have "\<dots> \<le> p \<cdot> (\<top> \<sqinter> (p\<^sup>\<circ> \<cdot> x))"
    using modular3 by blast
  also have "\<dots> = p \<cdot> p \<cdot> x"
    by (simp add: h local.convdqka.subid_conv mult_assoc)
  finally show "x \<le> p \<cdot> x"
    by (metis h local.dual_order.trans local.mult_1_left qdual.qd.mult_isol)
qed

lemma lla: "p \<le> 1 \<Longrightarrow> ((do x \<le> p) = (x \<le> p \<cdot> \<top>))"
  apply standard
  apply (smt (verit) lla_top_aux local.do_def local.inf.assoc local.inf.cobounded2 local.inf.commute local.inf.idem local.inf.orderE modular_2 qdual.qd.oner)
proof -
  assume a1: "x \<le> p \<cdot> \<top>"
  assume a2: "p \<le> 1"
  have f3: "x \<cdot> \<top> \<le> p \<cdot> \<top> \<cdot> \<top>"
    using a1 qdual.qd.dd.mult_iso by auto
  have f4: "p \<cdot> do x \<le> p"
    by (metis (full_types) local.do_le_top local.inf.bounded_iff local.mult.monoid_axioms local.order.partial_preordering_axioms monoid.right_neutral partial_preordering.refl qdual.qd.dd.mult_iso)
  have "x \<cdot> \<top> \<le> p \<cdot> \<top>"
    using f3 by (simp add: local.mult.semigroup_axioms semigroup.assoc)
  then show "do x \<le> p"
    using f4 a2 lla_top_aux local.do_le_top local.inf.bounded_iff local.order_trans by blast
qed


lemma do_top: "do x = 1 \<sqinter> (x \<cdot> \<top>)"
proof-
  have "1 \<sqinter> (x \<cdot> \<top>) = 1 \<sqinter> (x \<cdot> (\<top> \<sqinter> x\<^sup>\<circ> \<cdot> 1))"
    by (metis local.inf.commute local.inf_top.left_neutral modular_1)
  also have "\<dots> = do x"
    by (simp add: local.do_def)
  finally show ?thesis..
qed

lemma do_absorp: "x \<le> do x \<cdot> x"
proof-
  have "x = x \<sqinter> (x \<cdot> 1)"
    by simp
  also have "\<dots> \<le> (1 \<sqinter> (x \<cdot> x\<^sup>\<circ>)) \<cdot> x"
    using local.inf.absorb_iff2 modular_2 by force
  also have "\<dots> = do x \<cdot> x"
    by (simp add: local.do_def)
  finally show ?thesis.
qed

lemma do_absorp_eq [simp]: "do x \<cdot> x = x"
  by (metis do_absorp do_subid local.mult_1_left local.order.antisym qdual.qd.mult_isol)

lemma do_top2: "x \<cdot> \<top> = do x \<cdot> \<top>"
proof (rule order.antisym)
  have "x \<cdot> \<top> = do x \<cdot> x \<cdot> \<top>"
    by simp
  also have "\<dots> \<le> do x \<cdot> \<top> \<cdot> \<top>"
    using local.order_refl local.top_greatest qdual.qd.mult_iso by presburger
  also have "\<dots> = do x \<cdot> \<top>"
    by (simp add: local.mult.semigroup_axioms semigroup.assoc)
  finally show "x \<cdot> \<top> \<le> do x \<cdot> \<top>".
  have "do x \<cdot> \<top> = (1 \<sqinter> (x \<cdot> \<top>)) \<cdot> \<top>"
    by (simp add: do_top)
  also have "\<dots> \<le> (1 \<cdot> \<top>) \<sqinter> (x \<cdot> \<top> \<cdot> \<top>)"
    using qdual.qd.mult_isol by auto
  also have "\<dots> = x \<cdot> \<top>"
    by (simp add: mult_assoc)
  finally show "do x \<cdot> \<top> \<le> x \<cdot> \<top>".
qed

lemma do_local [simp]: "do (x \<cdot> do y) = do (x \<cdot> y)"
proof-
  have "do (x \<cdot> do y) = 1 \<sqinter> (x \<cdot> do y \<cdot> \<top>)"
    using do_top by force
  also have "\<dots> = 1 \<sqinter> (x \<cdot> y \<cdot> \<top>)"
    by (metis do_top2 local.qdual.mult_assoc)
  also have "\<dots> = do (x \<cdot> y)"
    by (simp add: do_top)
  finally show ?thesis
    by force
qed

lemma do_inf: "do (x \<sqinter> y) = 1 \<sqinter> (y \<cdot> x\<^sup>\<circ>)"
  by (smt (z3) do_absorp_eq invqka.inv_one local.do_def local.inf_commute local.inv_binf local.inv_contrav local.inv_invol local.mult_1_right modular_1 modular_2 mult_assoc)

lemma "do (x \<squnion> y) \<le> do x \<squnion> do y"
  unfolding do_top
  nitpick (* no proof no counterexample *)
  oops

lemma 
  fixes f::"'a \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_absorb: "\<forall>x. x \<le> f x \<cdot> x"
  and f_local: "\<forall>x y. f (x \<cdot> f y) = f (x \<cdot> y)"
  and f_add: "\<forall>x y. f (x \<squnion> y) = f x \<squnion> f y"
  and f_subid: "\<forall>x. f x \<le> \<top>"
  and f_zero: "f \<bottom> = \<bottom>"
  and g_absorb: "\<forall>x. x \<le> g x \<cdot> x"
  and g_local: "\<forall>x y. g (x \<cdot> g y) = g (x \<cdot> y)"
  and g_add: "\<forall>x y. g (x \<squnion> y) = g x \<squnion> g y"
  and g_subid: "\<forall>x. g x \<le> \<top>"
  and g_zero: "g \<bottom> = \<bottom>"
shows "f = g" 
  nitpick[show_all]
  oops

end

class distributive_dedekind_quantale = distributive_quantale + dedekind_quantale

begin

text \<open>In distributive modular quantales we can derive all domain axioms.\<close>

lemma do_sup [simp]: "do (x \<squnion> y) = do x \<squnion> do y"
proof-
  have "do (x \<squnion> y) = 1 \<sqinter> ((x \<squnion> y) \<cdot> \<top>)"
    by (simp add: local.do_top)
  also have "\<dots> = 1 \<sqinter> (x \<cdot> \<top> \<squnion> y \<cdot> \<top>)"
    by (simp add: qdual.qd.distl)
  also have "\<dots> = (1 \<sqinter> (x \<cdot> \<top>)) \<squnion> (1 \<sqinter> (y \<cdot> \<top>))"
    by (simp add: local.inf_sup_distrib1)
  also have "\<dots> = do x \<squnion> do y"
    by (simp add: local.do_top)
  finally show ?thesis.
qed

lemma 
  fixes f::"'a \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_absorb: "\<forall>x. x \<le> f x \<cdot> x"
  and f_local: "\<forall>x y. f (x \<cdot> f y) = f (x \<cdot> y)"
  and f_add: "\<forall>x y. f (x \<squnion> y) = f x \<squnion> f y"
  and f_subid: "\<forall>x. f x \<le> \<top>"
  and f_zero: "f \<bottom> = \<bottom>"
  and g_absorb: "\<forall>x. x \<le> g x \<cdot> x"
  and g_local: "\<forall>x y. g (x \<cdot> g y) = g (x \<cdot> y)"
  and g_add: "\<forall>x y. g (x \<squnion> y) = g x \<squnion> g y"
  and g_subid: "\<forall>x. g x \<le> \<top>"
  and g_zero: "g \<bottom> = \<bottom>"
shows "f = g" 
  nitpick[show_all]
  oops

end

sublocale distributive_dedekind_quantale \<subseteq> modal_kleene_algebra "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar cd do
  apply unfold_locales
             apply (simp add: local.cd_def local.inf.absorb_iff2)
            apply (metis local.do_inv local.do_local local.inv_contrav local.inv_do)
           apply (metis local.do_inv local.do_sup local.inv_binsup)
          apply (simp add: local.cd_def)+
      apply (simp add: local.do_top local.inf_sup_distrib1 qdual.qd.distl)
  by (simp_all add: local.do_subid)

class boolean_dedekind_quantale = boolean_quantale + dedekind_quantale

begin

lemma inv_neg: "(-x)\<^sup>\<circ> = -(x\<^sup>\<circ>)"
  by (metis invqka.inv_sup invqka.inv_zero local.compl_unique local.inf_compl_bot local.inv_binf local.inv_top local.sup_compl_top)

lemma residuation: "x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  using local.compl_le_swap1 local.inf_compl_bot local.inf_shunt local.schroeder_1 by blast

end

lemma (in involutive_quantale) dedekind_modular:
  assumes "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  shows "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  using assms local.inf_le1 local.order_trans qdual.qd.mult_isor by blast

lemma (in distributive_involutive_quantale) schroeder_modular:
  assumes "\<forall>x y z. ((x \<cdot> y) \<sqinter> z = \<bottom>) = (y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>)"
  and "\<forall>x y z. ((x \<cdot> y) \<sqinter> z = \<bottom>) = (x \<sqinter> (z \<cdot> y\<^sup>\<circ>) = \<bottom>)"
  and "((x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>) = ((y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>)"
shows "\<forall>x y z. (x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  nitpick (* counterexample *)
  oops

lemma (in involutive_quantale)
  assumes "\<forall>x y z w. (y \<sqinter> (z \<cdot> x\<^sup>\<circ>) \<le> w \<longrightarrow> (y \<cdot> x) \<sqinter> z \<le> w \<cdot> x)"
  shows "\<forall>x y z. (x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  using assms by blast

lemma (in involutive_quantale)
  assumes "\<forall>x y z. (x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  shows "\<forall>w x y z.  (y \<sqinter> (z \<cdot> x\<^sup>\<circ>) \<le> w \<longrightarrow> (y \<cdot> x) \<sqinter> z \<le> w \<cdot> x)"
  using assms local.order_trans qdual.qd.mult_isol by blast

lemma (in boolean_involutive_quantale) res_peirce: 
  assumes "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows  "((x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>) = ((y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>)"
proof
  assume "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>"
  hence "z\<^sup>\<circ> \<le> -(x \<cdot> y)"
    by (simp add: local.inf.commute local.inf_shunt)
  thus "(y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
    by (metis assms local.dual_order.trans local.inf_shunt local.inv_conjugate local.inv_contrav local.inv_invol qdual.qd.mult_isor)
next 
  assume "(y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
  hence "x\<^sup>\<circ> \<le> -(y \<cdot> z)"
    using local.compl_le_swap1 local.inf_shunt by blast
  thus "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>"
    by (smt (verit, ccfv_SIG) assms local.inf_shunt local.inv_conjugate local.inv_contrav local.le_sup_iff local.sup_absorb2 qdual.qd.distr)
qed

lemma (in boolean_involutive_quantale) res_schroeder1: 
  assumes "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows "((x \<cdot> y) \<sqinter> z = \<bottom>) = (y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>)"
proof
  assume h: "(x \<cdot> y) \<sqinter> z = \<bottom>"
  hence "z \<le> -(x \<cdot> y)"
    by (simp add: local.inf.commute local.inf_shunt)
  thus "y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>"
    by (meson assms local.compl_le_swap1 local.inf_shunt local.order_trans qdual.qd.mult_isor)
next 
  assume "y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>"
  hence "y \<le> -(x\<^sup>\<circ> \<cdot> z)"
    by (simp add: local.inf_shunt)
  thus "(x \<cdot> y) \<sqinter> z = \<bottom>"
    by (metis assms local.inf_shunt local.inv_invol local.order_trans qdual.qd.mult_isor)
qed

lemma (in boolean_involutive_quantale) res_schroeder2: 
  assumes "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows "((x \<cdot> y) \<sqinter> z = \<bottom>) = (x \<sqinter> (z \<cdot> y\<^sup>\<circ>) = \<bottom>)"
  by (metis assms local.inv_invol local.res_peirce local.res_schroeder1)

lemma (in boolean_involutive_quantale) res_mod:
  assumes  "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
proof-
  have "(x \<cdot> y) \<sqinter> z = ((x \<sqinter> ((z \<cdot> y\<^sup>\<circ>) \<squnion> -(z \<cdot> y\<^sup>\<circ>))) \<cdot> y) \<sqinter> z"
    by simp
  also have "\<dots> = (((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<sqinter> z) \<squnion> (((x \<sqinter> -(z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<sqinter> z)"
    using local.inf_sup_distrib1 local.inf_sup_distrib2 qdual.qd.distl by presburger 
  also have "\<dots> \<le> ((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<squnion> ((x \<cdot> y) \<sqinter> (-(z \<cdot> y\<^sup>\<circ>)) \<cdot> y \<sqinter> z)"
    by (metis assms local.inf.cobounded1 local.inf.commute local.inf_compl_bot_right local.res_schroeder2 local.sup_bot_right)
  also have "\<dots> \<le> ((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<squnion> ((x \<cdot> y) \<sqinter> -z  \<sqinter> z)"
    by (metis assms local.inf.commute local.inf_compl_bot_right local.res_schroeder2 local.sup.cobounded1 local.sup_bot_right)
  also have "\<dots> \<le> ((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y)"
    by (simp add: local.inf.commute)
  finally show ?thesis.
qed


class involutive_modal_quantale = modal_quantale + involutive_quantale

sublocale involutive_modal_quantale \<subseteq> invmqmka: involutive_modal_kleene_algebra "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar invol cod dom..

context involutive_modal_quantale
begin 

lemma "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  nitpick (* 3-element counterexample *)
  oops

lemma "x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x \<Longrightarrow> dom x \<le> x \<cdot> x\<^sup>\<circ>"
  nitpick (* 3-element counterexample *)
  oops

lemma "dom (x\<^sup>\<circ>) = cod x"
  nitpick (* 4-element counterexample *)
  oops

lemma "dom x \<le> do x"
  nitpick 
  oops 

lemma do_approx_dom: "do x \<le> dom x"
proof -
  have "do x = dom (do x) \<cdot> do x"
    by simp
  also have "\<dots> \<le> dom (1 \<sqinter> (x \<cdot> x\<^sup>\<circ>))"
    by (metis local.do_def local.inf.cobounded1 local.mult_1_right qdual.qd.mult_isor)
  also have "\<dots> \<le> dom 1 \<sqinter> dom (x \<cdot>  x\<^sup>\<circ>)"
    using local.dom_meet_sub by presburger
  also have "\<dots> \<le> dom (x \<cdot> dom (x\<^sup>\<circ>))"
    by simp
  also have "\<dots> \<le> dom x"
    using local.dom_meet local.dqmka.d_export_var local.inf.absorb_iff2 by presburger
  finally show ?thesis.
qed

end

class modal_quantale_converse = involutive_modal_quantale + quantale_converse

sublocale modal_quantale_converse \<subseteq> invmqmka: modal_kleene_algebra_converse "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar invol cod dom
  by (unfold_locales, simp add: local.strong_gelfand)

class modal_quantale_strong_converse = involutive_modal_quantale + 
  assumes weak_dom_def: "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  and weak_cod_def: "cod x \<le> x\<^sup>\<circ> \<cdot> x"

sublocale modal_quantale_strong_converse \<subseteq> invmqmka: modal_kleene_algebra_strong_converse "1" "(\<cdot>)" "(\<squnion>)" "\<bottom>" "(\<le>)" "(<)" qstar invol cod dom
  by (unfold_locales, simp_all add: local.weak_dom_def local.weak_cod_def)

context modal_quantale_strong_converse
begin

lemma "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  nitpick (* 5-element counterexample *)
  oops

lemma dom_def: "dom x = 1 \<sqinter> (x \<cdot> x\<^sup>\<circ>)"
  apply (rule order.antisym)
  apply (simp add: local.dom_subid local.weak_dom_def)
  by (smt (verit, best) local.dom_subid local.dqmka.d_absorb_eq local.dqmka.d_iso local.dual_order.trans local.inf.cobounded1 local.inf.cobounded2 local.mqs.msrdual.cod_local local.mult_1_right qdual.qd.mult_isor)

lemma cod_def: "cod x = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> x)"
  by (metis invqka.inv_one local.cd_compat local.coddual.dqmka.d_absorb_eq local.coddual.dqmka.d_export_var local.dc_compat local.dom_def local.dqmka.d_absorb_eq local.dqmka.d_export local.inv_binf local.inv_contrav local.inv_invol)

lemma "do x = dom x"
  by (simp add: local.do_def local.dom_def)

end

class dedekind_modal_distributive_quantale = involutive_modal_quantale + dedekind_quantale + distributive_quantale

begin

lemma "dom x = do x"
  nitpick (* 3-element counterexample *)
  oops

end

class dedekind_modal_boolean_quantale = involutive_modal_quantale + dedekind_quantale + boolean_quantale

begin

lemma subid_idem: "p \<le> 1 \<Longrightarrow> p \<cdot> p = p"
  by (metis (full_types) local.convdqka.subid_conv local.do_absorp local.do_def local.dual_order.antisym local.eq_refl local.inf_absorb2 local.mult_1_right qdual.qd.dd.mult_iso)

lemma subid_comm: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<cdot> q = q \<cdot> p"
  by (smt (verit, ccfv_SIG) local.dual_order.antisym local.dual_order.trans local.mult_1_left local.mult_1_right local.qdual.mult_assoc qdual.qd.mult_isol qdual.qd.mult_isor subid_idem)

lemma subid_meet_comp: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<sqinter> q = p \<cdot> q"
  by (smt (verit, ccfv_SIG) local.inf.absorb2 local.inf.assoc local.inf.cobounded1 local.inf.cobounded2 local.inf.orderE local.mult_1_right qdual.qd.mult_isor subid_comm subid_idem)

lemma subid_dom: "p \<le> 1 \<Longrightarrow> dom p = p"
proof-
  assume h: "p \<le> 1"
  have a: "p \<squnion> (1 \<sqinter> -p) = 1"
    using h local.sup.absorb_iff2 local.sup_inf_distrib1 by auto
  have "(1 \<sqinter> -p) \<sqinter> p = \<bottom>"
    by (simp add: local.inf.commute)
  thus ?thesis
    by (smt (verit, best) a h local.dom_subid local.dom_zero local.dqmka.d_absorb_eq local.dqmka.d_id local.dqmka.d_iso local.inf.absorb1 local.inf_le1 local.mqs.msrdual.cod_local qdual.qd.distr subid_comm subid_meet_comp)
qed

lemma do_prop: "(do x \<le> do y) = (x \<le> do y \<cdot> \<top>)"
  by (metis local.do_absorp_eq local.do_top local.do_top2 local.inf_mono local.order_refl local.top_greatest local.top_top mult_assoc qdual.qd.mult_iso)

lemma "(do x \<le> do y) = (x \<le> do y \<cdot> x)"
  by (smt (verit, del_insts) do_prop local.do_absorp_eq local.eq_refl local.inf.absorb2 local.inf.coboundedI1 local.top_greatest qdual.qd.mult_iso)

lemma lla_subid: "p \<le> 1 \<Longrightarrow> ((dom x \<le> p) = (x \<le> p \<cdot> x))"
  by (metis local.dqmka.lla subid_dom)

lemma dom_do: "dom x = do x"
proof-
  have "x \<le> do x \<cdot> x"
    by simp
  hence "dom x \<le> do x"
    using lla_subid local.do_subid by auto
  thus ?thesis
    by (simp add: local.antisym_conv local.do_approx_dom)
qed

end

end
