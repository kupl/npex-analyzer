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
import random
from pprint import pprint
from typing import List
from dataclasses import asdict, dataclass, field, fields, is_dataclass

INFER_PATH = os.getenv("INFER_NPEX")
MVN_OPT = "-V -B -Denforcer.skip=true -Dcheckstyle.skip=true -Dcobertura.skip=true -Drat.skip=true -Dlicense.skip=true -Dfindbugs.skip=true -Dgpg.skip=true -Dskip.npm=true -Dskip.gulp=true -Dskip.bower=true"
ROOT_DIR = os.getcwd()
DEP_JAR_PATH = "/media/4tb/npex/NPEX_DATA/vfix_benchmarks/deps"


@dataclass
class Result:
    number_of_patches: int
    number_of_verified: int
    number_of_rejected: int
    time_to_verify: float
    verified_patches: List[str]
    rejected_patches: List[str]

    def __init__(self):
        self.number_of_patches = 0
        self.number_of_verified = 0
        self.number_of_rejected = 0
        self.time_to_verify = 0.0
        self.verified_patches = []
        self.rejected_patches = []

    def to_json(self):
        with open(f"{ROOT_DIR}/result.json", 'w') as json_file:
            json_file.write(json.dumps(asdict(self), indent=4))

    def add_result(self, patch, result):
        self.number_of_patches = self.number_of_patches + 1
        if result:
            self.number_of_verified = self.number_of_verified + 1
            self.verified_patches.append(patch)
        else:
            self.number_of_rejected = self.number_of_rejected + 1
            self.rejected_patches.append(patch)

def apply_patch(project_root_dir, patch_dir):
    with open(f"{patch_dir}/patch.json", "r") as f:
        patch_json = json.load(f)
    source_path_to_patch = f"{project_root_dir}/{patch_json['original_filepath']}"
    shutil.copyfile(f"{patch_dir}/patch.java", f"{source_path_to_patch}")
    shutil.copyfile(f"{patch_dir}/patch.json", f"{ROOT_DIR}/patch.json")





class Bug:
    project_root_dir: str
    build_type: str
    error_report_arg: str
    class_path: str

    def __init__(self, project_root_dir, error_reports):
        self.project_root_dir = project_root_dir
        self.error_reports_arg = " ".join(
            [f"--error-report {npe_path}" for npe_path in error_reports])
        if os.path.isfile(f"{project_root_dir}/pom.xml"):
            self.build_type = "mvn"
            self.class_path = None
        else:
            self.build_type = "javac"
            jar_path = ':'.join(glob.glob(f"{DEP_JAR_PATH}/*.jar"))
            self.class_path = f"{jar_path}:{self.project_root_dir}:{self.project_root_dir}/../target/classes"

    def checkout(self):
        if os.path.isfile("/media/4tb/npex/NPEX_DATA/vfix_benchmarks/.git/index.lock"):
            backoff = random.uniform(0.1, 2.0)
            time.sleep(backoff)
            self.checkout()
        
        ret = subprocess.run(f"git checkout -- {self.project_root_dir}", shell=True, cwd=self.project_root_dir)
        if ret.returncode == 128:
            backoff = random.uniform(0.1, 2.0)
            time.sleep(backoff)
            self.checkout()
            
        elif ret.returncode != 0:
            print(f"[FAIL] git checkout")
            exit(-1)
        

    def capture_all(self):
        self.checkout()
        if self.build_type == "mvn":
            build_cmd = f"mvn clean test-compile {MVN_OPT}"
        else:
            subprocess.run(f"javac -cp {self.class_path} {self.project_root_dir}/Main.java", shell=True, cwd=self.project_root_dir)
            java_files = glob.glob(f"{self.project_root_dir}/**/*.java", recursive=True)
            java_files_to_compile = [java_file for java_file in java_files if os.path.isfile(java_file.rstrip("java") + "class")]
            with open(f"{self.project_root_dir}/java_files", 'w') as f:
                java_files_str = "\n".join(java_files_to_compile)
                f.writelines(java_files_str)
            build_cmd = f"javac -cp {self.class_path} @{self.project_root_dir}/java_files"
            print(build_cmd)
        capture_cmd = f"{INFER_PATH} capture -- {build_cmd}"
        subprocess.run(capture_cmd, shell=True, cwd=self.project_root_dir)

    def inference(self):
        start_time = time.time()
        spec_inference_cmd = f"{INFER_PATH} npex --spec-checker-only --spec-inference {self.error_reports_arg}"
        ret = subprocess.run(spec_inference_cmd, shell=True, cwd=self.project_root_dir)
        if ret.returncode == 1:
            print(f"[FAIL] spec inference")
            exit(-1)
        elif ret.returncode != 0:
            print(f"[FAIL] spec inference")
            exit(ret.returncode)
        return time.time() - start_time

    def capture_incremental(self, patch_dir):
        if self.build_type == "mvn":
            build_cmd = f"mvn test-compile {MVN_OPT}"
        else:
            with open(f"{patch_dir}/patch.json", "r") as f:
                patch_json = json.load(f)
            patched_file = f"{self.project_root_dir}/{patch_json['original_filepath']}"
            build_cmd = f"javac -cp {self.class_path} {patched_file}"
        print(build_cmd)
        capture_cmd = f"{INFER_PATH} capture -- {build_cmd}"
        subprocess.run(capture_cmd, shell=True, cwd=self.project_root_dir)

    def verify(self, patch_dir):
        print(f"[Progress]: Verifying patch in directory {patch_dir}")
        print(f" - NPE-lists: {error_reports}")

        apply_patch(self.project_root_dir, patch_dir)
        self.capture_incremental(patch_dir)

        launch_spec_veri_cmd = f"{INFER_PATH} npex --spec-verifier --spec-checker-only {self.error_reports_arg}"
        print(f" - npex-verifier command: {launch_spec_veri_cmd}")
        return (subprocess.run(launch_spec_veri_cmd,
                               shell=True,
                               cwd=self.project_root_dir)).returncode

    def verify_all(self):
        start_time = time.time()
        patches_dir = f"{self.project_root_dir}/patches"

        result = Result()
        
        for patch_dir in glob.glob(f"{patches_dir}/*"):
            patch_id = os.path.basename(patch_dir)
            self.checkout()
            verify_result = self.verify(patch_dir)
            if verify_result == None or verify_result == -2:
                result.add_result(patch_id, False)
            elif verify_result == 0:
                result.add_result(patch_id, True)
            else:
                result.add_result(patch_id, False)
        
        result.time_to_verify = time.time() - start_time
        result.to_json()

        print(f'Result has been stored at: result.json')
        print(f'time to verify patches: {time.time() - start_time}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--error_reports", help="error reports")
    parser.add_argument("--patch_id", help="patch_id")
    parser.add_argument("--apply_patch", default=False, action='store_true', help="patch_id")
    parser.add_argument("--capture", default=False, action='store_true', help="patch_id")
    parser.add_argument("--inference", default=False, action='store_true', help="patch_id")
    parser.add_argument("--verify", default=False, action='store_true', help="patch_id")
    args = parser.parse_args()
    
    error_reports = glob.glob(
        "npe*.json") if args.error_reports == None else glob.glob(
            args.error_reports)
    pprint(f"Start inference by {error_reports}")
    bug = Bug(ROOT_DIR, error_reports)
    if args.apply_patch:
        patch_dir = f"{ROOT_DIR}/patches/{args.patch_id}"
        apply_patch(ROOT_DIR, patch_dir)
        bug.capture_incremental(patch_dir)
    elif args.capture:
        bug.capture_all()
    elif args.inference:
        bug.inference()
    elif args.verify:
        bug.verify_all()
    else:
        bug.capture_all()
        bug.inference()
        bug.verify_all()
