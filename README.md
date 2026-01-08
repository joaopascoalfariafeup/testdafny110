# TESTDAFNY110

This repository contains the **replication package** for the paper:

> **Automatic Generation of Formal Specification and Verification Annotations Using LLMs and Test Oracles**

The package includes the dataset, experimental results, scripts, and analysis artifacts required to reproduce the experiments and analyses reported in the paper.

---

## Repository Structure

**Unless explicitly indicated by a file extension (e.g., `.py`, `.xlsx`), all entries listed below are directories that contain multiple files and/or subdirectories.**

```text
.
├── dataset
│   ├── stripped_programs
│   ├── subsetA
│   ├── subsetB
│   └── subsetC
│
├── data_analysis
│   ├── analysis_of_success_factors.xlsx
│   ├── overall_results_and_analysis.xlsx
│   └── analysis_selected_solutions.xlsx
│
├── llm_generated_direct_prompting
│   ├── Claude_Opus_4.5_T=0
│   ├── Claude_Opus_4.5_T=0.5
│   ├── Deepseek_V3.2_T=0.5
│   ├── GPT_4_T=0.5
│   ├── GPT_5.2_R=Low
│   └── GPT_5.2_R=None
│
├── llm_generated_repair_prompting
│   ├── Claude_Opus_4.5_T=0
│   ├── Claude_Opus_4.5_T=0.5
│   ├── Claude_Opus_4.5_T=0.5_negative_tests
│   ├── Deepseek_V3.2_T=0.5
│   ├── GPT_4_T=0.5
│   ├── GPT_5.2_R=Low
│   ├── GPT_5.2_R=None
│   ├── Multimodel_selected_solutions
│   └── Multimodel_selected_solutions_minimized
│
└── python_scripts
    ├── analysis_of_success_factors.py
    ├── generator.py
    └── simplifier.py
```

## Folder Descriptions

### 📁 `dataset`
Directory containing the **TESTDAFNY110 dataset**, consisting of **110 Dafny programs**, organized into three subsets (`subsetA`, `subsetB`, `subsetC`).

Each subset directory contains multiple Dafny programs.  
The `stripped_programs` directory contains versions of the same programs with all formal specifications and verification annotations removed, serving as input for LLM-based generation.

---

### 📁 `llm_generated_direct_prompting`
Directory containing multiple subdirectories, each corresponding to a specific:
- large language model, and
- configuration (e.g., temperature or reasoning level),

and holding the generated annotations produced using the **direct prompting** strategy.

---

### 📁 `llm_generated_repair_prompting`
Directory containing multiple subdirectories, each corresponding to a specific:
- large language model, and
- configuration or repair variant (including negative tests and multi-model selection),

and holding the generated annotations produced using the **repair prompting** strategy.

---

### 📁 `python_scripts`
Directory containing the Python source files used in the experimental pipeline:

- `generator.py`  
  Implements LLM-based generation of formal specifications and verification annotations from stripped Dafny programs.

- `simplifier.py`  
  Performs minimization (simplification) of generated solutions while preserving correctness.

- `analysis_of_success_factors.py`  
  Performs statistical analysis of success factors using **logistic regression**.

---

### 📁 `data_analysis`
Directory containing analysis artifacts and result files:

- `overall_results_and_analysis.xlsx`  
  Raw performance results of LLM-based generation, together with derived metrics and charts.

- `analysis_selected_solutions.xlsx`  
  Detailed analysis of selected solutions for **108 out of the 110 problems**.

- `analysis_of_success_factors.xlsx`  
  Source data and results used for the logistic regression analysis.
