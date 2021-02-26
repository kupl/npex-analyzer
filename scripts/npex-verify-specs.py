#!/usr/bin/python3.8
import argparse
import time
import json
import glob
import os
import subprocess
import shutil
import csv
import sys
from pprint import pprint

INFER_PATH = os.getenv("INFER_NPEX")
MVN_OPT = "-V -B -Denforcer.skip=true -Dcheckstyle.skip=true -Dcobertura.skip=true -Drat.skip=true -Dlicense.skip=true -Dfindbugs.skip=true -Dgpg.skip=true -Dskip.npm=true -Dskip.gulp=true -Dskip.bower=true"
ROOT_DIR = os.getcwd()

def infer_spec(project_root_dir, maven_build_command=f"mvn clean test-compile {MVN_OPT}", error_reports=["npe.json"]):
    capture_cmd = f"{INFER_PATH} capture -- {maven_build_command}"
    # if (subprocess.run(capture_cmd, shell=True, cwd=project_root_dir)).returncode != 0:
    #     print(f"[FAIL] compilation")
    #     return None
    subprocess.run(capture_cmd, shell=True, cwd=project_root_dir)

    error_reports_arg = " ".join([f"--error-report {npe_path}" for npe_path in error_reports])
    spec_inference_cmd = f"{INFER_PATH} npex --spec-checker-only --spec-inference {error_reports_arg}"
    if (subprocess.run(spec_inference_cmd, shell=True, cwd=project_root_dir)).returncode != 0:
        print(f"[FAIL] spec inference")
        return exit(-1)
    
    return True


def checkout(project_root_dir):
    if (subprocess.run("git checkout -f", shell=True, cwd=project_root_dir)).returncode != 0:
        print(f"[FAIL] git checkout")
        exit(-1)
     

# Assume original buggy code is analyzed. So we don't need to clean compile it
def verify_patches(project_root_dir, maven_build_command=f"mvn test-compile {MVN_OPT}", error_reports=["npe.json"]):
    start_time = time.time()
    patches_dir = f"{project_root_dir}/patches"
    dicts = []
    fieldnames = ["patch_id"]
   
    checkout(project_root_dir)
    
    if infer_spec(project_root_dir, error_reports=error_reports) == None:
        return None
    
    for patch in glob.glob(f"{patches_dir}/*"):
        patch_id = os.path.basename(patch)
        result_dict = {"patch_id": patch_id, "result": None}
        result = verify_patch(project_root_dir, patch, maven_build_command, error_reports=error_reports)
        if result == None or result == -2:
            result_dict["result"] = "compile-failure"
        elif result == 0: 
            result_dict["result"] = "verified"
        else:
            result_dict["result"] = "not-verified"
        dicts.append(result_dict)
            
    result_path = f"{project_root_dir}/spec-checking-results.csv"
    with open(result_path, 'w', newline="") as f:
        writer = csv.DictWriter(f, ["patch_id", "result"])
        writer.writeheader() 
        writer.writerows(dicts)
    print(f'Result has been stored at: {result_path}')
    print(f'time to verify patches: {time.time() - start_time}')

def apply_patch(project_root_dir, patch_dir):
    with open(f"{patch_dir}/patch.json", "r") as f:
        patch_json = json.load(f)
    source_path_to_patch = f"{project_root_dir}/{patch_json['original_filepath']}"
    shutil.copy(f"{patch_dir}/patch.java", f"{source_path_to_patch}")
    shutil.copy(f"{patch_dir}/patch.json", f"{ROOT_DIR}/patch.json")   

def verify_patch(project_root_dir, patch_dir, maven_build_command, error_reports):
    print(f"[Progress]: Verifying patch in directory {patch_dir}")
    print(f" - NPE-lists: {error_reports}")
    
    apply_patch(project_root_dir, patch_dir)
    capture_cmd = f"{INFER_PATH} capture -- {maven_build_command}"
    # if (subprocess.run(capture_cmd, shell=True, cwd=project_root_dir)).returncode != 0:
    #     return None
    subprocess.run(capture_cmd, shell=True, cwd=project_root_dir)
    
    error_reports_arg = " ".join([f"--error-report {npe_path}" for npe_path in error_reports])

    launch_spec_veri_cmd = f"{INFER_PATH} npex --spec-verifier --spec-checker-only {error_reports_arg}"
    print(f" - npex-verifier command: {launch_spec_veri_cmd}")
    return (subprocess.run(launch_spec_veri_cmd, shell=True, cwd=project_root_dir)).returncode


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--error_reports", help="error reports")
    parser.add_argument("--patch_id", help="patch_id")
    parser.add_argument("--apply_patch", default=False, action='store_true' ,help="patch_id")
    args=parser.parse_args()
    
    if args.apply_patch:
        patch_dir = f"{ROOT_DIR}/patches/{args.patch_id}"
        apply_patch(ROOT_DIR, patch_dir)
    
    else:
        if args.error_reports == None:
            error_reports = glob.glob("npe*.json")
            verify_patches(ROOT_DIR, error_reports=error_reports)
        else:
            error_reports = glob.glob(args.error_reports)
            print(f"Start inference by {error_reports}")
            verify_patches(ROOT_DIR, error_reports=error_reports)
