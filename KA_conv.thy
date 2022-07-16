(* 
Title: Kleene Algebra with Converse
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Kleene algebra with converse\<close>

theory "KA_conv"
  imports KA_light

begin

text \<open>We start from involutive dioids and Kleene algebra and then add a so-called strong Gelfand property 
to obtain an operation of coverse that is closer to algebras of paths and relations.\<close>

subsection \<open>Involutive Kleene algebra\<close>

class invol_op = 
  fixes invol :: "'a \<Rightarrow> 'a" ("_\<^sup>\<circ>" [101] 100)

class involutive_dioid = dioid + invol_op +
  assumes inv_invol [simp]: "(x\<^sup>\<circ>)\<^sup>\<circ> = x"
  and inv_contrav [simp]: "(x \<cdot> y)\<^sup>\<circ> = y\<^sup>\<circ> \<cdot> x\<^sup>\<circ>"
  and inv_sup [simp]: "(x + y)\<^sup>\<circ> = x\<^sup>\<circ> + y\<^sup>\<circ>"

begin

lemma inv_zero [simp]: "0\<^sup>\<circ> = 0"
proof-
  have "0\<^sup>\<circ> = (0\<^sup>\<circ> \<cdot> 0)\<^sup>\<circ>"
    by simp
  also have "\<dots> = 0\<^sup>\<circ> \<cdot> (0\<^sup>\<circ>)\<^sup>\<circ>"
    using local.inv_contrav by blast
  also have "\<dots> =  0\<^sup>\<circ> \<cdot> 0"
    by simp
  also have "\<dots> = 0"
    by simp
  finally show ?thesis.
qed

lemma inv_one [simp]: "1\<^sup>\<circ> = 1"
proof-
  have "1\<^sup>\<circ> = 1\<^sup>\<circ> \<cdot> (1\<^sup>\<circ>)\<^sup>\<circ>"
    by simp
  also have "\<dots> = (1\<^sup>\<circ> \<cdot> 1)\<^sup>\<circ>"
    using local.inv_contrav by presburger
  also have "\<dots> = (1\<^sup>\<circ>)\<^sup>\<circ>"
    by simp
  also have "\<dots> = 1"
    by simp
  finally show ?thesis.
qed

lemma inv_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<circ> \<le> y\<^sup>\<circ>"
  by (metis local.inv_sup local.order_def)

lemma inv_adj: "(x\<^sup>\<circ> \<le> y) = (x \<le> y\<^sup>\<circ>)"
  using inv_iso by fastforce

end

text \<open>Here is an equivalent axiomatisation.\<close>

class involutive_dioid_alt = dioid +
  fixes inv_alt :: "'a \<Rightarrow> 'a" 
  assumes inv_alt: "(inv_alt x \<le> y) = (x \<le> inv_alt y)"
  and inv_alt_contrav [simp]: "inv_alt (x \<cdot> y) = inv_alt y \<cdot> inv_alt x"

sublocale involutive_dioid_alt \<subseteq> altinv: involutive_dioid inv_alt _ _ _ _ _ _ 
  apply unfold_locales
    apply simp_all
  using local.inv_alt local.order_eq_iff apply force
  by (meson local.add_lub local.dual_order.eq_iff local.inv_alt)

sublocale involutive_dioid \<subseteq> altinv: involutive_dioid_alt _ _ _ _ _ _ invol
  by (unfold_locales, simp_all add: local.inv_adj) 

class involutive_kleene_algebra = involutive_dioid + kleene_algebra

begin

lemma inv_star: "(x\<^sup>\<star>)\<^sup>\<circ> = (x\<^sup>\<circ>)\<^sup>\<star>"
proof (rule order.antisym)
  have "((x\<^sup>\<circ>)\<^sup>\<star>)\<^sup>\<circ> = (1 + (x\<^sup>\<circ>)\<^sup>\<star> \<cdot> x\<^sup>\<circ>)\<^sup>\<circ>"
    by simp
  also have "\<dots> = 1 + (x\<^sup>\<circ>)\<^sup>\<circ> \<cdot> ((x\<^sup>\<circ>)\<^sup>\<star>)\<^sup>\<circ>"
    using local.inv_contrav local.inv_one local.inv_sup by presburger
  finally have "1 + x \<cdot> ((x\<^sup>\<circ>)\<^sup>\<star>)\<^sup>\<circ> \<le> ((x\<^sup>\<circ>)\<^sup>\<star>)\<^sup>\<circ>"
    by simp
  hence "x\<^sup>\<star> \<le> ((x\<^sup>\<circ>)\<^sup>\<star>)\<^sup>\<circ>"
    using local.star_inductl by force
  thus "(x\<^sup>\<star>)\<^sup>\<circ> \<le> (x\<^sup>\<circ>)\<^sup>\<star>" 
    by (simp add: local.inv_adj)
next
  have "(x\<^sup>\<star>)\<^sup>\<circ> = (1 + x\<^sup>\<star> \<cdot> x)\<^sup>\<circ>"
    by simp
  also have "\<dots> = 1 + x\<^sup>\<circ> \<cdot> (x\<^sup>\<star>)\<^sup>\<circ>"
    using local.inv_contrav local.inv_one local.inv_sup by presburger
  finally have "1 + x\<^sup>\<circ> \<cdot> (x\<^sup>\<star>)\<^sup>\<circ> \<le> (x\<^sup>\<star>)\<^sup>\<circ>"
    by simp
  thus "(x\<^sup>\<circ>)\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<circ>"
    using local.star_inductl by force
qed

end


subsection \<open>Kleene algebra with converse\<close>

text \<open>The name "strong Gelfand property" has been borrowed from Palmigiano and Re.\<close>

class dioid_converse = involutive_dioid +
  assumes strong_gelfand: "x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"

lemma (in dioid_converse) subid_conv: "x \<le> 1 \<Longrightarrow> x\<^sup>\<circ> = x"
proof (rule order.antisym)
  assume h: "x \<le> 1"
  have "x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"
    by (simp add: local.strong_gelfand)
  also have "\<dots> \<le> 1 \<cdot> x\<^sup>\<circ> \<cdot> 1"
    using h local.dd.mult_iso local.mult_isor by presburger
  also have "\<dots> =  x\<^sup>\<circ>"
    by simp
  finally show "x \<le> x\<^sup>\<circ>"
    by simp
  thus "x\<^sup>\<circ> \<le> x"
    by (simp add: local.inv_adj)
qed

lemma (in involutive_dioid)
  shows  "\<exists>f. (\<forall>x. x \<le> f x \<cdot> x) \<and> (\<forall>x y. f (x \<cdot> f y) = f (x \<cdot> y)) \<and> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>x. f x \<le> 1) \<and> (f 0 = 0)"
  nitpick (* 3-element counterexample *)
  oops

lemma (in dioid_converse)
  shows  "\<exists>f. (\<forall>x. x \<le> f x \<cdot> x) \<and> (\<forall>x y. f (x \<cdot> f y) = f (x \<cdot> y)) \<and> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>x. f x \<le> 1) \<and> (f 0 = 0)"
  nitpick (* no proof no counterexample *)
  oops


class kleene_algebra_converse = involutive_kleene_algebra + dioid_converse

end
