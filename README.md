# NPEX Analyzer
NPEX-analyzer is NPEX's symbolic executor which infers speification and validate patches by the inferred specification. NPEX-analyzer is built on top of [Infer(v1.0)](https://github.com/facebook/infer/releases/tag/v1.0.0). Please see [NPEX](https://github.com/kupl/npex) to see full usage of NPEX.

## How To Inference Specification

### Preparing Inputs
To infer an specification for a given NPE, we need to prepare the following inputs:
* Buggy Program (compilable by maven or javac)
* [NPE Information](https://github.com/AnonNPEX/AnonNPEX/blob/main/raw_results/npex/Activiti_0d83e98/input/npe.json) (Location of NPE: filepath, line, NPE expression)
* [Stack Trace](https://github.com/AnonNPEX/AnonNPEX/blob/main/raw_results/npex/Activiti_0d83e98/input/traces.json) (Stack trace of NPE)
* Alternative Expressions 

### Running Specification Inference
1. Capture the program by Infer IR.
2. Infer an specification for the given NPE.
3. Inferred specification will be stored at "npex-summaries" directory.

## How To Validate Patches
### Preparing Patches
* [Patch.java](https://github.com/AnonNPEX/AnonNPEX/tree/main/raw_results/npex/Activiti_0d83e98/patches/SkipReturnStrategy_125-125_2/patch.java)
* [Original filepath of patch.java](https://github.com/AnonNPEX/AnonNPEX/tree/main/raw_results/npex/Activiti_0d83e98/patches/SkipReturnStrategy_125-125_2/patch.json)
* [Patched lines of the patch code](https://github.com/AnonNPEX/AnonNPEX/tree/main/raw_results/npex/Activiti_0d83e98/patches/SkipReturnStrategy_125-125_2/patch.json)

### Running Patch Validation
1. Apply patch to a original program.
2. Compile a patched program.
3. Validate a patched program w.r.t. the inferred specification.

## Installation
See [INSTALL.md](./INSTALL.md).

## License
NPEX Anlayzer is MIT-licensed.
Note: Installation may download and install components licensed under the GPL.
