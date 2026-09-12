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
│   ├── original_programs
│   ├── stripped_programs
│   ├── subsetA
│   ├── subsetB
│   └── subsetC
│
├── data_analysis
│   ├── analysis_of_success_factors.xlsx
│   ├── overall_results_and_analysis.xlsx
│   ├── analysis_selected_solutions.xlsx
│   └── comparison_lu_et_al.csv
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
├── user_study
│   └── artifacts_of_user_study.pdf
│
└── python_scripts
    ├── abblation_rettach.py
    ├── analysis_of_success_factors.py
    ├── generator.py
    ├── simplifier.py
    └── .env.example
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

and holding the generated solutions (annotated programs) produced using the **direct prompting** strategy.

---

### 📁 `llm_generated_repair_prompting`
Directory containing multiple subdirectories, each corresponding to a specific:
- large language model, and
- configuration or repair variant (including negative tests and multi-model selection),

and holding the generated solutions (annotated programs) produced using the **repair prompting** strategy.

---

### 📁 `python_scripts`
Directory containing the Python source files used in the experimental pipeline:

- `generator.py`  
  Implements LLM-based generation of formal specifications and verification annotations from stripped Dafny programs.

- `simplifier.py`  
  Performs minimization (simplification) of generated solutions while preserving correctness.

- `analysis_of_success_factors.py`  
  Performs statistical analysis of success factors using **logistic regression**.

- `abblation_retach.py`  
  Performs the abblation experiments to determine the impact of test oracles and prompts.
---

### 📁 `data_analysis`
Directory containing analysis artifacts and result files:

- `overall_results_and_analysis.xlsx`  
  Raw performance results of LLM-based generation, together with derived metrics and charts.

- `analysis_selected_solutions.xlsx`  
  Detailed analysis of selected solutions for **108 out of the 110 problems**.

- `analysis_of_success_factors.xlsx`  
  Source data and results used for the logistic regression analysis.

- `comparison_lu_et_al.csv`  
  Per-task comparison with the approach of Lu et al. (Sec. 8.2 of the paper), covering the 123 MBPP-DFY tasks of their benchmark. Columns: `mbpp_task_id`; `lu_subset` (DFY-26 or DFY-97); `file_in_testdafny110` and `shared_with_testdafny110`; `lu_success`; `ours_success_multimodel_repair`; and `comment`.

  ### 📁 `user_study`
Directory containing the artifacts of the user study described in our paper:

- `artifacts_user_study.pdf`  
  Describes the user instructions, experimental_exercises and feedback questionnaire.


## Environment Variables

To use the Python scripts, create a '.env' file defining relevant variables. 

### --- API keys ---
OPENAI_API_KEY=
ANTHROPIC_API_KEY=
DEEPSEEK_API_KEY=

### --- Dafny ---
DAFNY_EXECUTABLE=

### --- generator.py ---
TESTDAFNY_INPUT_FOLDER=
TESTDAFNY_OUTPUT_FOLDER=

### --- simplifier.py ---
TESTDAFNY_STRIPPED_FOLDER=
TESTDAFNY_GENERATED_FOLDER=
TESTDAFNY_SIMPLIFIED_FOLDER=

### --- ablation A1 --- 
TESTDAFNY_DISABLE_TEST_ORACLES=0
