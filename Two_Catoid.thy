(* 
Title: 2-Catoids
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>2-Catoids\<close>

theory Two_Catoid
  imports Catoid

begin

text\<open>We define 2-catoids and in particular (strict) 2-categories as local functional 2-catoids. With Isabelle
we first need to make two copies of catoids for the 0-structure and 1-structure.\<close>

subsection \<open>0-structures and 1-structures.\<close>

text \<open>We could define the n-catoids and omega-catoids directly. But how can I add i to a subscript?\<close>

class multimagma0 = 
  fixes mcomp0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" (infixl "\<odot>\<^sub>0" 70) 

begin 

sublocale mm0: multimagma mcomp0.

abbreviation "\<Delta>\<^sub>0 \<equiv> mm0.\<Delta>"

abbreviation conv0 :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "*\<^sub>0" 70) where
 "X *\<^sub>0 Y \<equiv> mm0.conv X Y"

lemma "X *\<^sub>0 Y = \<Union>{x \<odot>\<^sub>0 y |x y. x \<in> X \<and> y \<in> Y}"
  by (simp add: mm0.conv_def)

end

class multimagma1 = 
  fixes mcomp1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" (infixl "\<odot>\<^sub>1" 70) 

begin 

sublocale mm1: multimagma mcomp1.

abbreviation "\<Delta>\<^sub>1 \<equiv> mm1.\<Delta>"

abbreviation conv1 :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "*\<^sub>1" 70) where
  "X *\<^sub>1 Y \<equiv> mm1.conv X Y"

end

class multisemigroup0 = multimagma0 +
  assumes assoc: "\<Union>{x \<odot>\<^sub>0 v |v. v \<in> y \<odot>\<^sub>0 z} = \<Union>{v \<odot>\<^sub>0 z |v. v \<in> x \<odot>\<^sub>0 y}"

sublocale multisemigroup0 \<subseteq> msg0: multisemigroup mcomp0
  by (unfold_locales, simp add: local.assoc)

class multisemigroup1 = multimagma1 +
  assumes assoc: "\<Union>{x \<odot>\<^sub>1 v |v. v \<in> y \<odot>\<^sub>1 z} = \<Union>{v \<odot>\<^sub>1 z |v. v \<in> x \<odot>\<^sub>1 y}"

sublocale  multisemigroup1 \<subseteq> msg1: multisemigroup mcomp1
  by (unfold_locales, simp add: local.assoc)

class st_multimagma0 = multimagma0 + 
fixes \<sigma>\<^sub>0 :: "'a \<Rightarrow> 'a"
  and \<tau>\<^sub>0 :: "'a \<Rightarrow> 'a" 
  assumes Dst0: "x \<odot>\<^sub>0 y \<noteq> {} \<Longrightarrow> \<tau>\<^sub>0 x = \<sigma>\<^sub>0 y"
  and src0_absorb [simp]: "\<sigma>\<^sub>0 x \<odot>\<^sub>0 x = {x}" 
  and tgt0_absorb [simp]: "x \<odot>\<^sub>0 \<tau>\<^sub>0 x = {x}"

sublocale st_multimagma0 \<subseteq> stmm0: st_multimagma mcomp0 \<sigma>\<^sub>0 \<tau>\<^sub>0
  by (unfold_locales, simp_all add: local.Dst0)

abbreviation (in st_multimagma0) 
  "s0fix \<equiv> stmm0.sfix"

abbreviation (in st_multimagma0)
  "t0fix \<equiv> stmm0.tfix"

abbreviation (in st_multimagma0)
  "Src\<^sub>0 \<equiv> stmm0.Src"

abbreviation (in st_multimagma0)
  "Tgt\<^sub>0 \<equiv> stmm0.Tgt"

class st_multimagma1 = multimagma1 + 
fixes \<sigma>\<^sub>1 :: "'a \<Rightarrow> 'a" 
  and \<tau>\<^sub>1 :: "'a \<Rightarrow> 'a"
  assumes Dst1: "x \<odot>\<^sub>1 y \<noteq> {} \<Longrightarrow> \<tau>\<^sub>1 x = \<sigma>\<^sub>1 y"
  and src1_absorb [simp]: "\<sigma>\<^sub>1 x \<odot>\<^sub>1 x = {x}" 
  and tgt1_absorb [simp]: "x \<odot>\<^sub>1 \<tau>\<^sub>1 x = {x}"

sublocale  st_multimagma1 \<subseteq> stmm1:  st_multimagma mcomp1  \<sigma>\<^sub>1 \<tau>\<^sub>1
  by (unfold_locales, simp_all add: local.Dst1)

abbreviation (in st_multimagma1)
  "s1fix \<equiv> stmm1.sfix"

abbreviation (in st_multimagma1)
  "t1fix \<equiv> stmm1.tfix"

abbreviation (in st_multimagma1)
  "Src\<^sub>1 \<equiv> stmm1.Src"

abbreviation (in st_multimagma1)
  "Tgt\<^sub>1 \<equiv> stmm1.Tgt"

class catoid0 = st_multimagma0 + multisemigroup0

sublocale catoid0 \<subseteq> stmsg0: catoid mcomp0 \<sigma>\<^sub>0 \<tau>\<^sub>0..

class catoid1 = st_multimagma1 + multisemigroup1

sublocale catoid1 \<subseteq> stmsg1: catoid mcomp1 \<sigma>\<^sub>1 \<tau>\<^sub>1..

class local_catoid0 = catoid0 +
  assumes src0_local: "Src\<^sub>0 (x \<odot>\<^sub>0 \<sigma>\<^sub>0 y) \<subseteq> Src\<^sub>0 (x \<odot>\<^sub>0 y)"
  and tgt0_local: "Tgt\<^sub>0 (\<tau>\<^sub>0 x \<odot>\<^sub>0 y) \<subseteq> Tgt\<^sub>0 (x \<odot>\<^sub>0 y)"

class local_catoid1 = catoid1 +
  assumes l1_local: "Src\<^sub>1 (x \<odot>\<^sub>1 \<sigma>\<^sub>1 y) \<subseteq> Src\<^sub>1 (x \<odot>\<^sub>1 y)"
  and r1_local: "Tgt\<^sub>1 (\<tau>\<^sub>1 x \<odot>\<^sub>1 y) \<subseteq> Tgt\<^sub>1 (x \<odot>\<^sub>1 y)"

sublocale local_catoid0 \<subseteq> ssmsg0: local_catoid mcomp0 \<sigma>\<^sub>0 \<tau>\<^sub>0
  apply unfold_locales
  using local.src0_local apply presburger
  using local.tgt0_local by blast

sublocale local_catoid1 \<subseteq> stmsg1: local_catoid mcomp1 \<sigma>\<^sub>1 \<tau>\<^sub>1
  apply unfold_locales using local.l1_local local.r1_local by auto

class functional_magma0 = multimagma0 + 
  assumes functionality0: "x \<in> y \<odot>\<^sub>0 z \<Longrightarrow> x' \<in> y \<odot>\<^sub>0 z \<Longrightarrow> x = x'"

sublocale functional_magma0 \<subseteq> pm0: functional_magma mcomp0
  by (unfold_locales, simp add: local.functionality0)

class functional_magma1 = multimagma1 + 
  assumes functionality1: "x \<in> y \<odot>\<^sub>1 z \<Longrightarrow> x' \<in> y \<odot>\<^sub>1 z \<Longrightarrow> x = x'"

sublocale functional_magma1 \<subseteq> pm1: functional_magma mcomp1
  by (unfold_locales, simp add: local.functionality1)

class functional_semigroup0 = functional_magma0 + multisemigroup0

sublocale functional_semigroup0 \<subseteq> psg0: functional_semigroup mcomp0..

class functional_semigroup1 = functional_magma1 + multisemigroup1

sublocale functional_semigroup1 \<subseteq> psg1: functional_semigroup mcomp1..

class functional_catoid0 = functional_semigroup0 + catoid0

sublocale functional_catoid0 \<subseteq> psg0: functional_catoid mcomp0  \<sigma>\<^sub>0 \<tau>\<^sub>0..

class functional_catoid1 = functional_semigroup1 + catoid1

sublocale functional_catoid1 \<subseteq> psg1: functional_catoid mcomp1 \<sigma>\<^sub>1 \<tau>\<^sub>1..

class single_set_category0 = functional_catoid0 + local_catoid0

sublocale single_set_category0 \<subseteq> sscat0: single_set_category mcomp0 \<sigma>\<^sub>0 \<tau>\<^sub>0..

class single_set_category1 = functional_catoid1 + local_catoid1

sublocale single_set_category1 \<subseteq> sscat1: single_set_category mcomp1  \<sigma>\<^sub>1 \<tau>\<^sub>1..


subsection \<open>2-Catoids\<close>

text \<open>Next we define 2-catoids and 2-categories.\<close>

class two_st_multimagma = st_multimagma0 + st_multimagma1 +
  assumes comm_s0s1: "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
  and comm_s0t1: "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
  and comm_t0s1: "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
  and comm_t0t1: "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"
  assumes interchange: "(w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) \<subseteq> (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)"
  and s1_hom: "Src\<^sub>1 (x \<odot>\<^sub>0 y) = \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 y"
  and t1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) = \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y"
  and s0_weak_hom: "Src\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y"
  and t0_weak_hom: "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<tau>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>0 y"
  and s1s0 [simp]: "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"
  and s1t0 [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x"
  and t1s0 [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"
  and t1t0 [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x"

sublocale two_st_multimagma \<subseteq> twolropp: two_st_multimagma "\<lambda>x y. y \<odot>\<^sub>0 x" "\<tau>\<^sub>0" "\<sigma>\<^sub>0" "\<lambda>x y. y \<odot>\<^sub>1 x" "\<tau>\<^sub>1" "\<sigma>\<^sub>1"
  apply unfold_locales
                    apply (simp_all add: stmm0.stopp.Dst stmm1.stopp.Dst comm_t0t1 comm_t0s1 comm_s0t1 comm_s0s1 s1_hom t1_hom s0_weak_hom t0_weak_hom)
  by (metis local.interchange local.stmm0.stopp.conv_exp local.stmm1.stopp.conv_exp multimagma.conv_exp)

lemma (in two_st_multimagma) s0s1 [simp]: 
  "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>0 x"
  by (simp add: local.comm_s0s1)

lemma (in two_st_multimagma) s0t1 [simp]: 
  "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<sigma>\<^sub>0 x"
  by (simp add: local.comm_s0t1)

lemma (in two_st_multimagma) t0s1: 
  "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<tau>\<^sub>0 x"
  by simp

lemma (in two_st_multimagma) t1t1: 
  "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>0 x"
  by simp

text \<open>We lift the axioms to the powerset level.\<close>

lemma (in two_st_multimagma) comm_S0S1: 
  "Src\<^sub>0 (Src\<^sub>1 X) = Src\<^sub>1 (Src\<^sub>0 X)"
  by (simp add: image_image)

lemma (in two_st_multimagma) comm_T0T1: 
  "Tgt\<^sub>0 (Tgt\<^sub>1 X) = Tgt\<^sub>1 (Tgt\<^sub>0 X)"
  using local.twolropp.comm_S0S1 by presburger

lemma (in two_st_multimagma) comm_S0T1: 
  "Src\<^sub>0 (Tgt\<^sub>1 x) = Tgt\<^sub>1 (Src\<^sub>0 x)"
  by (simp add: image_image)

lemma (in two_st_multimagma) comm_T0S1: 
  "Tgt\<^sub>0 (Src\<^sub>1 x) = Src\<^sub>1 (Tgt\<^sub>0 x)"
  using local.twolropp.comm_S0T1 by presburger

lemma (in two_st_multimagma) interchange_lifting: 
  "(W *\<^sub>1 X) *\<^sub>0 (Y *\<^sub>1 Z) \<subseteq> (W *\<^sub>0 Y) *\<^sub>1 (X *\<^sub>0 Z)"
proof-
  {fix a
  assume "a \<in> (W *\<^sub>1 X) *\<^sub>0 (Y *\<^sub>1 Z)"
  hence "\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. a \<in> (w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z)"
    by (smt (verit, del_insts) mm0.conv_exp2 mm1.conv_exp2)
  hence "\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. a \<in> (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)"
    using local.interchange by blast
  hence "a \<in> (W *\<^sub>0 Y) *\<^sub>1 (X *\<^sub>0 Z)"
    by (smt (verit, del_insts) multimagma.conv_exp2)}
  thus ?thesis..
qed

lemma (in two_st_multimagma) Src1_hom: 
  "Src\<^sub>1 (X *\<^sub>0 Y) = Src\<^sub>1 X *\<^sub>0 Src\<^sub>1 Y" 
proof-
  {fix a 
  have "(a \<in> Src\<^sub>1 (X *\<^sub>0 Y)) = (\<exists>b \<in> X *\<^sub>0 Y. a = \<sigma>\<^sub>1 b)"
    by blast
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Y. a = \<sigma>\<^sub>1 b \<and> b \<in> c \<odot>\<^sub>0 d)"
    by (metis multimagma.conv_exp2)
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src\<^sub>1 (c \<odot>\<^sub>0 d))"
    by blast
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> \<sigma>\<^sub>1 c \<odot>\<^sub>0 \<sigma>\<^sub>1 d)"
    using local.s1_hom by presburger
  also have "\<dots> = (\<exists>c \<in> Src\<^sub>1 X. \<exists>d \<in> Src\<^sub>1 Y. a \<in> c \<odot>\<^sub>0 d)"
    by blast
  also have "\<dots> = (a \<in> Src\<^sub>1 X *\<^sub>0 Src\<^sub>1 Y)"
    using local.mm0.conv_exp2 by auto  
  finally have "(a \<in> Src\<^sub>1 (X *\<^sub>0 Y)) = (a \<in> Src\<^sub>1 X *\<^sub>0 Src\<^sub>1 Y)".}
  thus ?thesis
    by force
qed

lemma (in two_st_multimagma) codcomp: 
  "Tgt\<^sub>1 (X *\<^sub>0 Y) = Tgt\<^sub>1 X *\<^sub>0 Tgt\<^sub>1 Y" 
proof-
  {fix a 
  have "(a \<in> Tgt\<^sub>1 (X *\<^sub>0 Y)) = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Tgt\<^sub>1 (c \<odot>\<^sub>0 d))"
    by (smt (verit, best) image_iff multimagma.conv_exp2)
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> \<tau>\<^sub>1 c \<odot>\<^sub>0 \<tau>\<^sub>1 d)"
    using local.t1_hom by presburger
  also have "\<dots> = (a \<in> Tgt\<^sub>1 X *\<^sub>0 Tgt\<^sub>1 Y)"
    using local.mm0.conv_exp2 by auto  
  finally have "(a \<in> Tgt\<^sub>1 (X *\<^sub>0 Y)) = (a \<in> Tgt\<^sub>1 X *\<^sub>0 Tgt\<^sub>1 Y)".}
  thus ?thesis
    by force
qed

lemma (in two_st_multimagma) Src0_weak_hom: 
  "Src\<^sub>0 (X *\<^sub>1 Y) \<subseteq> Src\<^sub>0 X *\<^sub>1 Src\<^sub>0 Y" 
proof-
  {fix a
  assume "a \<in> Src\<^sub>0 (X *\<^sub>1 Y)"
  hence "\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src\<^sub>0 (c \<odot>\<^sub>1 d)"
    using local.mm1.conv_exp2 by fastforce
  hence "\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> \<sigma>\<^sub>0 c \<odot>\<^sub>1 \<sigma>\<^sub>0 d"
    using local.s0_weak_hom by blast
  hence "a \<in> Src\<^sub>0 X *\<^sub>1 Src\<^sub>0 Y"
    using local.mm1.conv_exp2 by auto}
  thus ?thesis
    by force
qed

lemma (in two_st_multimagma) Tgt0_weak_hom: 
  "Tgt\<^sub>0 (X *\<^sub>1 Y) \<subseteq> Tgt\<^sub>0 X *\<^sub>1 Tgt\<^sub>0 Y" 
proof-
  {fix a
  assume "a \<in> Tgt\<^sub>0 (X *\<^sub>1 Y)"
  hence "\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Tgt\<^sub>0 (c \<odot>\<^sub>1 d)"
    using local.mm1.conv_exp2 by fastforce
  hence "\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> \<tau>\<^sub>0 c \<odot>\<^sub>1 \<tau>\<^sub>0 d"
    using local.t0_weak_hom by blast
  hence "a \<in> Tgt\<^sub>0 X *\<^sub>1 Tgt\<^sub>0 Y"
    using local.mm1.conv_exp2 by auto}
  thus ?thesis
    by force
qed

lemma (in two_st_multimagma) S1S0 [simp]: 
  "Src\<^sub>1 (Src\<^sub>0 X) = Src\<^sub>0 X"
  by force

lemma (in two_st_multimagma) S1T0 [simp]: 
  "Src\<^sub>1 (Tgt\<^sub>0 X) = Tgt\<^sub>0 X"
  by force

lemma (in two_st_multimagma) T1S0: 
  "Tgt\<^sub>1 (Src\<^sub>0 X) = Src\<^sub>0 X"
  by simp

lemma (in two_st_multimagma) T1T0: 
  "Tgt\<^sub>1 (Tgt\<^sub>0 X) = Tgt\<^sub>0 X"
  by simp

lemma (in two_st_multimagma) id1_comp0: 
  "s1fix *\<^sub>0 s1fix \<subseteq> s1fix"
proof-
  {fix a
  have "(a \<in> s1fix *\<^sub>0 s1fix) = (\<exists>b \<in> s1fix.\<exists>c \<in> s1fix. a \<in> b \<odot>\<^sub>0 c)"
    by (meson local.mm0.conv_exp2)
  also have "\<dots> = (\<exists>b c. a \<in> \<sigma>\<^sub>1 b \<odot>\<^sub>0 \<sigma>\<^sub>1 c)"
    by (metis image_iff local.stmm1.stopp.tfix_im rangeI)
  finally have "(a \<in> s1fix *\<^sub>0 s1fix) = (\<exists>b c. a \<in> Src\<^sub>1 (b \<odot>\<^sub>0 c))"
    using local.twolropp.t1_hom by presburger
  hence "(a \<in> s1fix *\<^sub>0 s1fix) \<Longrightarrow> (\<exists>b. a = \<sigma>\<^sub>1 b)"
    by blast
  hence  "(a \<in> s1fix *\<^sub>0 s1fix) \<Longrightarrow> (a \<in> s1fix)"
    using local.stmm1.stopp.Tgt_subid by blast}
  thus ?thesis
    by blast
qed

lemma (in two_st_multimagma) id1_comp0_eq [simp]: 
  "s1fix *\<^sub>0 s1fix = s1fix"
proof-
  {fix a
    have "(a \<in> s1fix) = (\<exists>b. a = \<sigma>\<^sub>1 b)"
      by (metis image_iff local.stmm1.stopp.tfix_im range_eqI)
    also have "\<dots> = (\<exists>b. a \<in> \<sigma>\<^sub>0 (\<sigma>\<^sub>1 b) \<odot>\<^sub>0 \<sigma>\<^sub>1 b)"
      using local.src0_absorb by blast
  finally have "(a \<in> s1fix) = (\<exists>b. a \<in> \<sigma>\<^sub>1 (\<sigma>\<^sub>0 b) \<odot>\<^sub>0 \<sigma>\<^sub>1 b)"
    by fastforce
  hence "(a \<in> s1fix) \<Longrightarrow> (\<exists>b c. a \<in> \<sigma>\<^sub>1 c \<odot>\<^sub>0 \<sigma>\<^sub>1 b)"
    by blast
  hence "(a \<in> s1fix) \<Longrightarrow> (a \<in> s1fix *\<^sub>0 s1fix)"
    by (metis (mono_tags, lifting) local.mm0.conv_exp2 local.stmm1.stopp.tfix_im range_eqI)}
  thus ?thesis
    using local.id1_comp0 by blast
qed

lemma (in two_st_multimagma) id01: 
  "s0fix \<subseteq> s1fix"
proof-
  {fix a
    have "(a \<in> s0fix) = (\<exists>b. a = \<sigma>\<^sub>0 b)"
      by (metis imageE local.stmm0.stopp.tfix_im rangeI)
    hence "(a \<in> s0fix) = (\<exists>b. a = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 b))"
    by fastforce
  hence "(a \<in> s0fix) \<Longrightarrow> (\<exists>b. a = \<sigma>\<^sub>1 b)"
    by blast
  hence "(a \<in> s0fix) \<Longrightarrow> (a \<in> s1fix)"
    using local.stmm1.stopp.tfix_im by blast}
  thus ?thesis
    by blast
qed


subsection\<open>2-Catoids and single-set 2-categories\<close>

class two_catoid = two_st_multimagma + catoid0 + catoid1

class local_two_catoid = two_st_multimagma + local_catoid0 + local_catoid1

class two_category = two_catoid + single_set_category0 + single_set_category1

lemma (in two_category) conv0_sgl: 
  "a \<in> x \<odot>\<^sub>0 y \<Longrightarrow> {a} = x \<odot>\<^sub>0 y"
  using local.functionality0 by fastforce

lemma (in two_category) conv1_sgl: 
  "a \<in> {x} *\<^sub>1 {y} \<Longrightarrow> {a} = {x} *\<^sub>1 {y}"
  using local.functionality1 local.mm1.conv_exp by force

text \<open>Next we derive some simple globular properties.\<close>

lemma (in two_category) strong_interchange_St1: 
  assumes "a \<in> (w \<odot>\<^sub>0 x) *\<^sub>1 (y \<odot>\<^sub>0 z)"
  shows "Tgt\<^sub>1 (w \<odot>\<^sub>0 x) = Src\<^sub>1 (y \<odot>\<^sub>0 z)"
  apply safe
  using assms local.Dst1 local.functionality0 local.stmm1.stopp.conv_exp2 apply fastforce
  by (smt (verit, ccfv_SIG) assms equals0D image_eqI local.Dst1 local.functionality0 local.mm1.conv_exp2)

lemma (in two_category) strong_interchange_ll0: 
  assumes "a \<in> (w \<odot>\<^sub>0 x) *\<^sub>1 (y \<odot>\<^sub>0 z)"
  shows "\<sigma>\<^sub>0 w = \<sigma>\<^sub>0 y"
  by (metis assms local.mm1.conv_exp2 local.s0s1 local.s0t1 local.stmsg1.ts_msg.src_comp_aux local.stmsg1.ts_msg.tgt_comp_aux stmsg0.src_comp_aux)

text \<open>There is no strong interchange law, and the homomorphism laws stay weak, too.\<close>

lemma (in two_category) "(w \<odot>\<^sub>1 y) *\<^sub>0 (x \<odot>\<^sub>1 z) = (w \<odot>\<^sub>0 x) *\<^sub>1 (y \<odot>\<^sub>0 z)"
  nitpick
  oops

lemma (in two_category) "R\<^sub>0 (x \<odot>\<^sub>1 y) = r\<^sub>0 x \<odot>\<^sub>1 r\<^sub>0 y"
  nitpick
  oops

lemma (in two_category) "L\<^sub>0 (x \<odot>\<^sub>1 y) = l\<^sub>0 x \<odot>\<^sub>1 l\<^sub>0 y"
  nitpick 
  oops
 
lemma (in two_category) "(W *\<^sub>0 Y) *\<^sub>1 (X *\<^sub>0 Z) = (W *\<^sub>1 X) *\<^sub>0 (Y *\<^sub>1 Z)"
  nitpick
  oops


subsection \<open>Reduced axiomatisations\<close>

class two_st_multimagma_red = st_multimagma0 + st_multimagma1 +
  assumes interchange: "(w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) \<subseteq> (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)" (* irredundant *)
  assumes src1_hom: "Src\<^sub>1 (x \<odot>\<^sub>0 y) = \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 y"  (* irredundant *)
  and tgt1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) = \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y" (* irredundant *)
  and src0_weak_hom: "Src\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y" (* no proof no counterexample *)
  and tgt0_weak_hom: "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y" (* no proof no counterexample *) 

lemma (in two_st_multimagma_red) s0t1s0 [simp]: 
  "\<sigma>\<^sub>0 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) = \<sigma>\<^sub>0 x"
proof-
  have "{\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)} = Tgt\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by (meson local.tgt1_hom)
  also have "\<dots> = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>1 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by simp
  also have "\<dots> = Tgt\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by (simp add: local.tgt1_hom)
  finally have "Tgt\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) \<noteq> {}"
    by force
  hence "\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<noteq> {}"
    by blast
  thus ?thesis
    using stmm0.s_absorb_var3 by auto
qed

lemma (in two_st_multimagma_red) t0s1s0 [simp]: 
  "\<tau>\<^sub>0 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)) = \<sigma>\<^sub>0 x"
proof-
  have "{\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)} = Src\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> =  \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by (meson local.src1_hom)
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)) \<odot>\<^sub>0 \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = Src\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x)"
    using local.src1_hom by force
  finally  have "Src\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x) \<noteq> {}"
    by force 
  hence "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x \<noteq> {}"
    by blast
  thus ?thesis
    by (simp add: local.Dst0)
qed

lemma (in two_st_multimagma_red) s1s0 [simp]: 
  "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"
proof-
  have "{\<sigma>\<^sub>0 x} = \<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>0 x"
    by simp
  also have "\<dots> = (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>1 \<sigma>\<^sub>0 x) *\<^sub>0 (\<sigma>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by (simp add: multimagma.conv_atom)
  also have "\<dots> \<subseteq> (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x) *\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    using local.interchange by blast
  also have "\<dots> = (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>0 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x))) *\<^sub>1 (\<sigma>\<^sub>0 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by simp
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    using local.mm1.conv_atom local.src0_absorb local.tgt0_absorb by presburger
  finally have "{\<sigma>\<^sub>0 x} \<subseteq> \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)".
  thus ?thesis
    by (metis empty_iff insert_subset singletonD stmm1.st_comm stmm1.st_prop stmm1.t_idem)
qed

lemma (in two_st_multimagma_red) s1t0 [simp]: 
  "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x"
  by (metis local.s1s0 local.stmm0.stopp.ts_compat)

lemma (in two_st_multimagma_red) t1s0 [simp]: 
  "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"
  by (simp add: stmm1.st_fix)

lemma (in two_st_multimagma_red) t1t0 [simp]: 
  "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x"
  by (simp add: stmm1.st_fix)

lemma (in two_st_multimagma_red) comm_s0s1: 
  "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
proof-
  have "{\<sigma>\<^sub>1 x} = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>1 x"
    by (smt (verit, best) local.Dst0 local.s1s0 local.src0_absorb local.src1_hom)
  also have "\<dots> = \<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>1 x"
    by simp
  finally have "\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>1 x \<noteq> {}"
    by force
  hence "\<tau>\<^sub>0 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)"
    by (meson local.Dst0)
  hence "\<sigma>\<^sub>0 x = \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)"
    by simp
  thus ?thesis
    by simp
qed

lemma (in two_st_multimagma_red) comm_s0t1: 
  "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
proof-
  have "{\<tau>\<^sub>1 x} = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>1 x"
    by (metis local.src0_absorb local.t1s0 local.tgt1_hom stmm0.s_absorb_var)
  hence "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>1 x \<noteq> {}"
    by force 
  hence "\<tau>\<^sub>0 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) = \<sigma>\<^sub>0 (\<tau>\<^sub>1 x)"
    using local.Dst0 by blast
  thus ?thesis
    by simp
qed

lemma (in two_st_multimagma_red) comm_t0s1: 
  "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
proof-
  have "{\<sigma>\<^sub>1 x} = \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
    by (metis local.s1t0 local.src1_hom local.stmm0.stopp.s_absorb_var local.tgt0_absorb)
  hence "\<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 (\<tau>\<^sub>0 x) \<noteq> {}"
    by force
  hence "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<tau>\<^sub>0 (\<sigma>\<^sub>1 (\<tau>\<^sub>0 x))"
    by (metis local.s1t0 local.stmm0.stopp.s_absorb_var stmm0.tt_idem)
  thus ?thesis
    by simp
qed

lemma (in two_st_multimagma_red) comm_t0t1: 
  "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"
  by (metis local.s1t0 local.stmm0.stopp.s_absorb_var3 local.tgt1_hom stmm1.st_fix)

lemma (in two_st_multimagma_red) "\<sigma>\<^sub>0 x = \<sigma>\<^sub>1 x"
  nitpick
  oops

lemma (in two_st_multimagma_red) "\<sigma>\<^sub>0 x = \<tau>\<^sub>1 x"
  nitpick
  oops 

lemma (in two_st_multimagma_red) "\<tau>\<^sub>0 x = \<tau>\<^sub>1 x"
  nitpick
  oops

lemma (in two_st_multimagma_red) "\<sigma>\<^sub>0 x = \<tau>\<^sub>0 x"
  nitpick
  oops
lemma (in two_st_multimagma_red) "\<sigma>\<^sub>1 x = \<tau>\<^sub>1 x"
  nitpick
  oops

lemma (in two_st_multimagma_red) "x \<odot>\<^sub>0 y = x \<odot>\<^sub>1 y"
  nitpick
  oops

lemma (in two_st_multimagma_red) "x \<odot>\<^sub>0 y = y \<odot>\<^sub>0 x"
  nitpick
  oops

lemma  (in two_st_multimagma_red) "x \<odot>\<^sub>1 y = y \<odot>\<^sub>1 x"
  nitpick
  oops

class two_catoid_red = catoid0 + catoid1 +
  assumes interchange: "(w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) \<subseteq> (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)" (* irredundant *)
  and s1_hom: "Src\<^sub>1 (x \<odot>\<^sub>0 y) = \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 y"  (* irredundant *)
  and t1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) = \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y" (* irredundant *)

lemma (in two_catoid_red) s0t1s0 [simp]: 
  "\<sigma>\<^sub>0 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) = \<sigma>\<^sub>0 x"
proof-
  have "{\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)} = Tgt\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    using local.t1_hom by blast
  also have "\<dots> = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>1 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by simp
  also have "\<dots> = Tgt\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by (simp add: local.t1_hom)
  finally have "Tgt\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) \<noteq> {}"
    by force
  hence "\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x) \<noteq> {}"
    by blast
  thus ?thesis
    using stmm0.s_absorb_var3 by blast
qed

lemma (in two_catoid_red) t0s1s0 [simp]: 
  "\<tau>\<^sub>0 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)) = \<sigma>\<^sub>0 x"
proof-
  have "{\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)} = Src\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
    using local.s1_hom by blast
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)) \<odot>\<^sub>0 \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = Src\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x)"
    using local.s1_hom by auto
  finally  have "Src\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x) \<noteq> {}"
    by force 
  hence "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x \<noteq> {}"
    by blast
  thus ?thesis
    by (simp add: local.Dst0)
qed

lemma (in two_catoid_red) s1s0 [simp]: 
  "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"
proof-
  have "{\<sigma>\<^sub>0 x} = \<sigma>\<^sub>0 x \<odot>\<^sub>0 \<sigma>\<^sub>0 x"
    by simp
  also have "\<dots> = (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>1 \<sigma>\<^sub>0 x) *\<^sub>0 (\<sigma>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by (simp add: multimagma.conv_atom)
  also have "\<dots> \<subseteq> (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<sigma>\<^sub>0 x) *\<^sub>1 (\<sigma>\<^sub>0 x \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    using local.interchange by blast
  also have "\<dots> = (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>0 \<tau>\<^sub>0 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x))) *\<^sub>1 (\<sigma>\<^sub>0 (\<tau>\<^sub>1 (\<sigma>\<^sub>0 x)) \<odot>\<^sub>0 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by simp
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    using local.mm1.conv_atom local.src0_absorb local.tgt0_absorb by presburger
  finally have "{\<sigma>\<^sub>0 x} \<subseteq> \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)".
  thus ?thesis
    using local.stmm1.stopp.Dst by fastforce
qed
 
lemma (in two_catoid_red) s1t0 [simp]: 
  "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x"
  by (metis local.s1s0 local.stmm0.stopp.ts_compat)

lemma (in two_catoid_red) t1s0 [simp]: 
  "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"
  by (simp add: stmm1.st_fix)

lemma (in two_catoid_red) t1t0 [simp]: 
  "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x"
  by (simp add: stmm1.st_fix)

lemma (in two_catoid_red) comm_s0s1: 
  "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
  by (metis local.s1_hom local.s1s0 stmm0.s_absorb_var)

lemma (in two_catoid_red) comm_s0t1: 
  "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
  by (metis local.t1_hom local.t1s0 stmm0.s_absorb_var)

lemma (in two_catoid_red) comm_t0s1: 
  "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
  by (metis empty_not_insert local.Dst0 local.s1_hom local.s1t0 local.tgt0_absorb)

lemma (in two_catoid_red) comm_t0t1: 
  "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"
  using local.t1_hom local.stmm0.stopp.s_absorb_var2 by fastforce

lemma (in two_catoid_red) s0_weak_hom: 
  "Src\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y"
proof cases
  assume "Src\<^sub>0 (x \<odot>\<^sub>1 y) = {}"
  thus ?thesis
    by auto 
next
  assume h: "Src\<^sub>0 (x \<odot>\<^sub>1 y) \<noteq> {}"
  hence h1: "\<tau>\<^sub>1 x = \<sigma>\<^sub>1 y"
    by (simp add: local.Dst1)
  hence "Src\<^sub>0 (x \<odot>\<^sub>1 y) = Src\<^sub>0 (Src\<^sub>1 (x \<odot>\<^sub>1 y))"
    unfolding image_def using local.comm_s0s1 by auto 
  also have "\<dots> = Src\<^sub>0 (Src\<^sub>1 (x \<odot>\<^sub>1 \<sigma>\<^sub>1 y))"
    using h stmsg1.src_local_cond by auto
  also have "\<dots> = Src\<^sub>0 (Src\<^sub>1 (x \<odot>\<^sub>1 \<tau>\<^sub>1 x))"
    using h1 by presburger
  also have  "\<dots> = {\<sigma>\<^sub>0 x}"
    by (simp add: local.comm_s0s1)
  also have "\<dots> = \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    using local.tgt1_absorb by presburger
  also have "\<dots> = \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<tau>\<^sub>1 x)"
    by (simp add: local.comm_s0t1)
  also have "\<dots> = \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<sigma>\<^sub>1 y)"
    by (simp add: h1)
  also have "\<dots> = \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y"
    by (simp add: local.comm_s0s1)
  finally show ?thesis
    by blast
qed

lemma (in two_catoid_red) t0_weak_hom: 
  "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<tau>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>0 y"

  by (metis equals0D image_subsetI insertI1 local.comm_t0s1 local.comm_t0t1 local.stmm1.stopp.Dst local.t1t0 local.tgt1_absorb stmsg1.tgt_comp_aux)


(*
subsection \<open>Cubical catoids\<close>

class cubical_two_st_multimagma = st_multimagma0 + st_multimagma1 +
  (*assumes comm_s0s1: "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"*)
  (*assumes comm_s0t1: "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"*)
  (*and comm_t0s1: "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"*)
  (*and comm_t0t1: "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"*)
  (*assumes interchange: "(w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) \<noteq> {} \<Longrightarrow> (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z) \<noteq> {} \<Longrightarrow> (w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) = (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)"*)
  assumes s1_hom: "Src\<^sub>1 (x \<odot>\<^sub>0 y) \<subseteq> \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 y"
  (*and t1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) \<subseteq> \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y"*)
  assumes s0_weak_hom: "Src\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y"
  (*and t0_weak_hom: "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<tau>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>0 y"*)
  assumes s1s0 [simp]: "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 (\<sigma>\<^sub>0 x)"
  (*and s1t0 [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<sigma>\<^sub>0 (\<tau>\<^sub>0 x)"*)
  (*and t1s0 [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<tau>\<^sub>0 (\<sigma>\<^sub>0 x)"*)
  (*and t1t0 [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 (\<tau>\<^sub>0 x)"*)
  and s1s0x [simp]: "\<sigma>\<^sub>1 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)"
  (*and s1t0x [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>1 x) = \<sigma>\<^sub>0 (\<tau>\<^sub>1 x)"*)
  (*and t1s0x [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>1 x) = \<tau>\<^sub>0 (\<sigma>\<^sub>1 x)"*)
  (*and t1t0x [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>1 x) = \<tau>\<^sub>0 (\<tau>\<^sub>1 x)"*)

begin

lemma bad1: "\<sigma>\<^sub>0 x = \<sigma>\<^sub>1 x"
  by (metis local.s1_hom local.s1s0 local.s1s0x local.src0_absorb local.src1_absorb local.stmm0.stopp.tt_idem stmm0.st_prop stmm0.ts_compat stmm1.s_export stmm1.s_ortho_iff subset_empty)

lemma bad2: "\<sigma>\<^sub>0 x = \<tau>\<^sub>0 x"
  by (metis empty_iff image_insert insert_subset local.Dst0 local.Dst1 local.s0_weak_hom local.s1_hom local.s1s0 local.s1s0x local.src1_absorb local.stmm0.stopp.ts_compat local.tgt0_absorb stmm0.ts_compat)

lemma bad3: "\<tau>\<^sub>0 x =\<tau>\<^sub>1 x"
  by (metis empty_not_insert ex_in_conv bad1 bad2 image_subset_iff local.Dst1 local.s0_weak_hom local.tgt1_absorb stmm1.ts_compat)

lemma bad4: "\<sigma>\<^sub>1 x =\<tau>\<^sub>1 x"
  using bad1 bad2 bad3 by fastforce

lemma comm_s0s1: "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
  by (metis bot.extremum_unique local.s0_weak_hom local.s1s0x local.src0_absorb local.src1_absorb local.stmm0.stopp.t_idem stmm0.s_export stmm1.s_absorb_var)

lemma comm_s0t1: "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
  by (metis bot.extremum_unique local.s0_weak_hom local.s1s0 local.src0_absorb local.stmm0.stopp.t_export local.stmm0.stopp.tt_idem local.tgt1_absorb stmm1.s_absorb_var3 stmm1.ts_compat)

lemma comm_t0s1: "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
  by (metis local.s1_hom local.s1s0 local.src1_absorb local.stmm0.stopp.s_absorb_var2 local.stmm0.stopp.ts_compat local.stmm1.stopp.t_export local.tgt0_absorb stmm1.s_ortho_iff subset_antisym)

lemma comm_t0t1: "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"
  using local.comm_s0s1 local.comm_s0t1 local.comm_t0s1 local.s1s0x by force
 
lemma t1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) \<subseteq> \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y"
  using local.comm_s0s1 local.comm_s0t1 local.s1_hom local.s1s0x local.stmm1.stopp.ts_compat stmm1.ts_compat by auto

lemma t0_weak_hom: "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<tau>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>0 y"
  using local.comm_s0s1 local.comm_t0s1 local.s0_weak_hom local.s1s0x by auto
  
lemma s1t0 [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<sigma>\<^sub>0 (\<tau>\<^sub>0 x)"
  by (metis local.s1s0 local.stmm0.stopp.ts_compat)

lemma t1s0 [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<tau>\<^sub>0 (\<sigma>\<^sub>0 x)"
  by (simp add: stmm1.st_fix)

lemma t1t0 [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 (\<tau>\<^sub>0 x)"
  by (simp add: stmm1.st_fix)

lemma s1t0x [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>1 x) = \<sigma>\<^sub>0 (\<tau>\<^sub>1 x)"
  using local.comm_s0s1 local.s1s0x by force

lemma t1s0x [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>1 x) = \<tau>\<^sub>0 (\<sigma>\<^sub>1 x)"
  by (metis local.s1s0x local.stmm1.stopp.tt_idem local.t1s0)

lemma t1t0x [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>1 x) = \<tau>\<^sub>0 (\<tau>\<^sub>1 x)"
  by (metis local.s1t0x local.stmm1.stopp.ts_compat local.t1s0)


lemma s0s1s0s0: "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>0 (\<sigma>\<^sub>0 x)"
  using local.comm_s0t1 local.comm_t0s1 local.comm_t0t1 local.s1t0x by auto
  
lemma s0t0t0s0: "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>0 (\<sigma>\<^sub>0 x)"
  by (simp add: local.comm_s0t1)

lemma t0s1s0t0: "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>0 (\<tau>\<^sub>0 x)"
  by (simp add: local.comm_t0s1)

lemma t0t1t0t0: "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>0 (\<tau>\<^sub>0 x)"
  by (simp add: local.comm_t0t1)

end

class cubical_two_catoid = cubical_two_st_multimagma + catoid0 + catoid1

begin

lemma "x \<odot>\<^sub>0 y = x \<odot>\<^sub>1 y"
  nitpick
  oops

lemma "x \<odot>\<^sub>0 y = y \<odot>\<^sub>0 x"
  nitpick
  oops

lemma "x \<odot>\<^sub>1 y = y \<odot>\<^sub>1 x"
  nitpick
  oops
*)

end






