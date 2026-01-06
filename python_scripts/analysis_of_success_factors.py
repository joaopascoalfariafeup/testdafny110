import pandas as pd
import numpy as np
import statsmodels.formula.api as smf
import statsmodels.api as sm
from sklearn.metrics import roc_curve, roc_auc_score
import matplotlib.pyplot as plt

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
    id_vars=["Program", "ProgLOC", "AnnotLOC", "HelperLOC"],
    value_vars=result_cols,
    var_name="Config",
    value_name="Success"
)
long["Config"] = long["Config"].str.replace("^Results_", "", regex=True)

# --------------------------------------------------
# 3. Fit logistic regression
# --------------------------------------------------

model = smf.glm(
    "Success ~ ProgLOC + AnnotLOC + HelperLOC + C(Config)",
    data=long,
    family=sm.families.Binomial()
).fit()

# --------------------------------------------------
# 4. Print coefficients (shared difficulty model)
# --------------------------------------------------

coef_names = ["Intercept", "ProgLOC", "AnnotLOC", "HelperLOC"]

coef_table = pd.DataFrame({
    "Coefficient": model.params.loc[coef_names],
    "StdErr": model.bse.loc[coef_names],
    "p-value": model.pvalues.loc[coef_names],
})

coef_table["OddsRatio"] = np.exp(coef_table["Coefficient"])

print("\n=== Shared model coefficients ===")
print(coef_table.round(4))

# Optional: print LLM configuration offsets
print("\n=== LLM configuration intercept offsets ===")
config_coefs = model.params[[c for c in model.params.index if c.startswith("C(Config)")]]
config_table = pd.DataFrame({
    "Offset": config_coefs,
    "OddsRatio": np.exp(config_coefs)
})
print(config_table.round(4))


# --------------------------------------------------
# 5. Predict probabilities
# --------------------------------------------------

long["p"] = model.predict(long)

# --------------------------------------------------
# 6. Global ROC curve and AUC
# --------------------------------------------------

fpr, tpr, _ = roc_curve(long["Success"], long["p"])
auc_global = roc_auc_score(long["Success"], long["p"])

plt.figure(figsize=(5, 4))
plt.plot(fpr, tpr, label=f"ROC curve (AUC = {auc_global:.3f})")
plt.plot([0, 1], [0, 1], linestyle="--", label="Random baseline")
plt.xlabel("False Positive Rate")
plt.ylabel("True Positive Rate")
plt.title("ROC Curve for Annotation Generation Success")
plt.legend()
plt.tight_layout()
plt.savefig("roc_curve.pdf")
plt.show()

# --------------------------------------------------
# 7. Per-LLM AUC computation
# --------------------------------------------------

auc_per_llm = (
    long.groupby("Config")
        .apply(lambda g: roc_auc_score(g["Success"], g["p"]))
        .reindex(config_order)
)

print("\n=== AUC per LLM configuration ===")
print(auc_per_llm.round(3))

# --------------------------------------------------
# 8. Horizontal bar chart with data labels
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
