import pandas as pd
import numpy as np
import statsmodels.formula.api as smf
import statsmodels.api as sm
from sklearn.metrics import roc_curve, roc_auc_score
import matplotlib.pyplot as plt
from scipy.stats import chi2

# --------------------------------------------------
# 1. Load data
# --------------------------------------------------

df = pd.read_excel("analysis_of_success_factors.xlsx")

# Identify result columns (14 LLM configurations)
result_cols = [c for c in df.columns if c.startswith("Results_")]

config_order = [c.replace("Results_", "") for c in result_cols]
config_order = list(reversed(config_order))

# --------------------------------------------------
# 2. Reshape to long format
# --------------------------------------------------

long = df.melt(
    id_vars=["Program", "ProgLOC", "AnnotLOC", "HelperLOC", "Dataset"],  # Added Dataset
    value_vars=result_cols,
    var_name="Config",
    value_name="Success"
)
long["Config"] = long["Config"].str.replace("^Results_", "", regex=True)

# Verify Dataset column
print("\n=== Dataset distribution ===")
print(long.groupby("Dataset")["Program"].nunique())
print(f"Total programs: {long['Program'].nunique()}")

# --------------------------------------------------
# 3. Fit logistic regression WITHOUT subdataset
# --------------------------------------------------

model_base = smf.glm(
    "Success ~ ProgLOC + AnnotLOC + HelperLOC + C(Config)",
    data=long,
    family=sm.families.Binomial()
).fit()

print("\n" + "="*60)
print("MODEL WITHOUT SUBDATASET")
print("="*60)

# --------------------------------------------------
# 4. Print coefficients (base model)
# --------------------------------------------------

coef_names = ["Intercept", "ProgLOC", "AnnotLOC", "HelperLOC"]

coef_table_base = pd.DataFrame({
    "Coefficient": model_base.params.loc[coef_names],
    "StdErr": model_base.bse.loc[coef_names],
    "z-value": model_base.tvalues.loc[coef_names],
    "p-value": model_base.pvalues.loc[coef_names],
})

coef_table_base["OddsRatio"] = np.exp(coef_table_base["Coefficient"])

print("\n=== Shared model coefficients (base model) ===")
print(coef_table_base.round(4))

# Print summary statistics
print(f"\nLog-likelihood: {model_base.llf:.2f}")
print(f"AIC: {model_base.aic:.2f}")
print(f"BIC: {model_base.bic:.2f}")

# --------------------------------------------------
# 4b. Robustness: the observations are not independent
# --------------------------------------------------
# Each program contributes one observation per configuration (14 in total), and
# those are correlated. Treating them as independent understates the standard
# errors, so we re-estimate the same model with standard errors clustered by
# program, and additionally with a random intercept per program. The point
# estimates are unchanged by construction; what changes is their significance.

TERMS = ["ProgLOC", "AnnotLOC", "HelperLOC"]

model_clustered = smf.glm(
    "Success ~ ProgLOC + AnnotLOC + HelperLOC + C(Config)",
    data=long,
    family=sm.families.Binomial()
).fit(cov_type="cluster", cov_kwds={"groups": long["Program"]})

print("\n" + "="*60)
print("ROBUSTNESS: STANDARD ERRORS CLUSTERED BY PROGRAM")
print("="*60)
for term in TERMS:
    print(f"  {term:10} coef={model_base.params[term]:+.4f}"
          f"  se(indep)={model_base.bse[term]:.4f} p={model_base.pvalues[term]:.3g}"
          f"  |  se(clustered)={model_clustered.bse[term]:.4f}"
          f" p={model_clustered.pvalues[term]:.3g}")

try:
    model_re = smf.mixedlm(
        "Success ~ ProgLOC + AnnotLOC + HelperLOC + C(Config)",
        data=long, groups=long["Program"]).fit()
    print("\n=== Random intercept per program (signs and ordering only) ===")
    for term in TERMS:
        print(f"  {term:10} coef={model_re.params[term]:+.4f}"
              f" se={model_re.bse[term]:.4f} p={model_re.pvalues[term]:.3g}")
except Exception as exc:
    print(f"\nRandom-intercept model not fitted: {type(exc).__name__}: {exc}")

# --------------------------------------------------
# 5. Fit logistic regression WITH subdataset
# --------------------------------------------------

model_with_dataset = smf.glm(
    "Success ~ ProgLOC + AnnotLOC + HelperLOC + C(Config) + C(Dataset)",
    data=long,
    family=sm.families.Binomial()
).fit()

print("\n" + "="*60)
print("MODEL WITH SUBDATASET")
print("="*60)

# --------------------------------------------------
# 6. Print coefficients (model with subdataset)
# --------------------------------------------------

# Structural features
coef_table_with = pd.DataFrame({
    "Coefficient": model_with_dataset.params.loc[coef_names],
    "StdErr": model_with_dataset.bse.loc[coef_names],
    "z-value": model_with_dataset.tvalues.loc[coef_names],
    "p-value": model_with_dataset.pvalues.loc[coef_names],
})

print("\n=== Shared model coefficients (with subdataset) ===")
print(coef_table_with.round(4))

# Subdataset coefficients
dataset_coefs = model_with_dataset.params[[c for c in model_with_dataset.params.index 
                                            if c.startswith("C(Dataset)")]]
dataset_table = pd.DataFrame({
    "Coefficient": dataset_coefs,
    "StdErr": model_with_dataset.bse[dataset_coefs.index],
    "z-value": model_with_dataset.tvalues[dataset_coefs.index],
    "p-value": model_with_dataset.pvalues[dataset_coefs.index],
    "OddsRatio": np.exp(dataset_coefs)
})

print("\n=== Subdataset coefficients (relative to reference level) ===")
print(dataset_table.round(4))

# Print summary statistics
print(f"\nLog-likelihood: {model_with_dataset.llf:.2f}")
print(f"AIC: {model_with_dataset.aic:.2f}")
print(f"BIC: {model_with_dataset.bic:.2f}")

# --------------------------------------------------
# 7. Likelihood-ratio test
# --------------------------------------------------

print("\n" + "="*60)
print("LIKELIHOOD-RATIO TEST")
print("="*60)

lr_stat = -2 * (model_base.llf - model_with_dataset.llf)
df_diff = len(model_with_dataset.params) - len(model_base.params)
p_value_lr = 1 - chi2.cdf(lr_stat, df_diff)

print(f"\nNull hypothesis: Subdataset has no effect (after controlling for complexity)")
print(f"LR statistic (χ²): {lr_stat:.2f}")
print(f"Degrees of freedom: {df_diff}")
print(f"p-value: {p_value_lr:.4f}")

if p_value_lr < 0.05:
    print("Result: REJECT null hypothesis (subdataset has significant effect)")
else:
    print("Result: FAIL TO REJECT null hypothesis (subdataset has no significant effect)")

# --------------------------------------------------
# 8. Compare AUCs
# --------------------------------------------------

long["p_base"] = model_base.predict(long)
long["p_with_dataset"] = model_with_dataset.predict(long)

auc_base = roc_auc_score(long["Success"], long["p_base"])
auc_with_dataset = roc_auc_score(long["Success"], long["p_with_dataset"])

print("\n=== AUC Comparison ===")
print(f"AUC without subdataset: {auc_base:.3f}")
print(f"AUC with subdataset:    {auc_with_dataset:.3f}")
print(f"Difference:             {auc_with_dataset - auc_base:.3f}")

# --------------------------------------------------
# 9. Global ROC curve (using base model)
# --------------------------------------------------

fpr, tpr, _ = roc_curve(long["Success"], long["p_base"])

plt.figure(figsize=(4.5, 3.5))
plt.plot(fpr, tpr, label=f"ROC curve (AUC = {auc_base:.3f})")
plt.plot([0, 1], [0, 1], linestyle="--", label="Random baseline")
plt.xlabel("False Positive Rate")
plt.ylabel("True Positive Rate")
plt.title("ROC Curve for Annotation Generation Success")
plt.legend()
plt.tight_layout()
plt.savefig("roc_curve.pdf")
plt.show()

# --------------------------------------------------
# 10. Per-LLM AUC computation (base model)
# --------------------------------------------------

auc_per_llm = (
    long.groupby("Config")
        .apply(lambda g: roc_auc_score(g["Success"], g["p_base"]))
        .reindex(config_order)
)

print("\n=== AUC per LLM configuration (base model) ===")
print(auc_per_llm.round(3))
print(f"\nAUC range: {auc_per_llm.min():.3f} - {auc_per_llm.max():.3f}")

# --------------------------------------------------
# 11. Horizontal bar chart with data labels
# --------------------------------------------------

plt.figure(figsize=(8, 4))
bars = plt.barh(auc_per_llm.index, auc_per_llm.values)

plt.xlabel("AUC-ROC")
plt.title("AUC per LLM Configuration")
plt.xlim(0.5, 1.0)

for bar in bars:
    width = bar.get_width()
    plt.text(
        width + 0.005,
        bar.get_y() + bar.get_height() / 2,
        f"{width:.2f}",
        va="center"
    )

plt.tight_layout()
plt.savefig("auc_per_llm.pdf")
plt.show()

# --------------------------------------------------
# 12. Per-subdataset success rates (for Table 4 analysis)
# --------------------------------------------------

print("\n" + "="*60)
print("PER-SUBDATASET ANALYSIS")
print("="*60)

# Average success rate by subdataset across all configurations
subdataset_success = (
    long.groupby("Dataset")["Success"]
    .mean()
    .sort_index()
)

print("\n=== Average success rate by subdataset ===")
for dataset, rate in subdataset_success.items():
    n_programs = long[long["Dataset"] == dataset]["Program"].nunique()
    print(f"{dataset}: {rate:.1%} ({n_programs} programs)")

# ANOVA-like test: compare means across subdatasets
# This gives you an alternative p-value
from scipy.stats import f_oneway

success_by_dataset = [
    long[long["Dataset"] == "A"]["Success"].values,
    long[long["Dataset"] == "B"]["Success"].values,
    long[long["Dataset"] == "C"]["Success"].values
]

f_stat, p_anova = f_oneway(*success_by_dataset)
print(f"\n=== One-way ANOVA on success rates ===")
print(f"F-statistic: {f_stat:.2f}")
print(f"p-value: {p_anova:.4f}")

# --------------------------------------------------
# 13. Summary for paper
# --------------------------------------------------

print("\n" + "="*60)
print("SUMMARY FOR PAPER")
print("="*60)

print(f"""
Key findings:

1. Structural feature coefficients (base model):
   - ProgLOC:   β = {model_base.params['ProgLOC']:.4f} (p < 0.001)
   - AnnotLOC:  β = {model_base.params['AnnotLOC']:.4f} (p < 0.001)
   - HelperLOC: β = {model_base.params['HelperLOC']:.4f} (p < 0.001)

2. Model discrimination:
   - AUC (base model): {auc_base:.3f}
   - AUC range across configs: {auc_per_llm.min():.2f} - {auc_per_llm.max():.2f}

3. Subdataset effect:
   - Likelihood-ratio test: χ²({df_diff}) = {lr_stat:.2f}, p = {p_value_lr:.3f}
   - AUC improvement: {auc_with_dataset - auc_base:.3f}
   - One-way ANOVA: F = {f_stat:.2f}, p = {p_anova:.3f}
   
4. Conclusion:
   {'Subdataset origin has NO significant effect' if p_value_lr > 0.05 else 'Subdataset origin HAS significant effect'}
   after controlling for structural complexity.
""")