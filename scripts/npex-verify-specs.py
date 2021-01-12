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
NPEX_SUMMARY_DIR = f"{ROOT_DIR}/npex-summaries"
NPEX_ORIGINAL_SUMMARY_DIR = f"{ROOT_DIR}/npex-original-summaries"


# Assume original buggy code is analyzed. So we don't need to clean compile it
def verify_patches(project_root_dir, maven_build_command=f"mvn test-compile {MVN_OPT}", error_reports=["npe.json"]):
    start_time = time.time()
    patches_dir = f"{project_root_dir}/patches"
    dicts = []
    fieldnames = ["patch_id"]
    for patch in glob.glob(f"{patches_dir}/*"):
        patch_id = os.path.basename(patch)
        result_path = verify_patch(project_root_dir, patch, maven_build_command, error_reports)
        if result_path == None:
            continue
        with open(result_path, "r", newline="") as csvfile:
            reader = csv.DictReader(csvfile)
            if len(fieldnames) == 1:
                fieldnames.extend(reader.fieldnames)
            row = next(reader)
            if len(set(list(row.values()))) < 2:
                continue
            row["patch_id"] = patch_id
            dicts.append(row)
    worthy_features = extract_interesting_features(dicts, project_root_dir)
    worthy_features.insert(0, worthy_features.pop(worthy_features.index('patch_id')))
    for d in dicts:
        for k in list(d.keys()):
            if not k in worthy_features:
                d.pop(k)
    result_path = f"{project_root_dir}/spec-checking-results.csv"
    with open(result_path, 'w', newline="") as f:
        writer = csv.DictWriter(f, worthy_features)
        writer.writeheader() 
        writer.writerows(dicts)
    print(f'Spec sheet has been stored at: {result_path}')
    print(f'time to verify patches: {time.time() - start_time}')

def extract_interesting_features(dicts, project_root_dir):
    assert (len(dicts) > 0)
    worthy_features, useless_features = [], []
    for feature in list(dicts[0].keys()):
        if len(set([d[feature] for d in dicts])) > 1:
            worthy_features.append(feature)
        else:
            useless_features.append(feature)
    print(f'Worthy Features (at least two separate patches are distinguished by each feature):')
    pprint(f'{worthy_features[:-1]}')
    os.chdir(project_root_dir)
    for feature in worthy_features[:-1]:
        os.system(f"cat specs/{feature}.text")
    return worthy_features

def verify_patch(project_root_dir, patch_dir, maven_build_command, error_reports):
    print(f"Verifying patch in directory: {patch_dir}")
    patch_source_path = f"{patch_dir}/patch.java"
    patch_json_path = f"{patch_dir}/patch.json"
    with open(patch_json_path, "r") as f:
        patch_json = json.load(f)
    
    source_path_to_patch = f"{project_root_dir}/{patch_json['original_filepath']}"
    with open(f"{project_root_dir}/changed_files", 'w') as f:
        f.write(source_path_to_patch)
        f.close()
        
    shutil.copyfile(patch_source_path, source_path_to_patch)
    shutil.copy2(patch_json_path, project_root_dir)
    
    # Prepare origianl summary except to_analyze
    shutil.rmtree(NPEX_SUMMARY_DIR)
    shutil.copytree(NPEX_ORIGINAL_SUMMARY_DIR, NPEX_SUMMARY_DIR)

    capture_cmd = f"{INFER_PATH} capture -- {maven_build_command}"
    if (subprocess.run(capture_cmd, shell=True, cwd=project_root_dir)).returncode != 0:
        return None
    
    # analyze_cmd = f"{INFER_PATH} analyze --biabduction-models-mode --spec-checker-only"
    # if (subprocess.run(analyze_cmd, shell=True, cwd=project_root_dir)).returncode != 0:
    #     return None

    npe_jsons = glob.glob(f"{project_root_dir}/{error_reports}")
    error_reports_arg = " ".join([f"--error-report {npe_path}" for npe_path in npe_jsons])

    launch_spec_veri_cmd = f"{INFER_PATH} npex --launch-spec-verifier --spec-checker-only {error_reports_arg}"
    if (subprocess.run(launch_spec_veri_cmd, shell=True, cwd=project_root_dir)).returncode != 0:
        return None

    debug_files = glob.glob(f"{project_root_dir}/*.debug")
    for debug_file in debug_files:
        path_to_store = f"{patch_dir}/{os.path.basename(debug_file)}"
        shutil.move(debug_file, path_to_store)


    return shutil.copy(
        f"{project_root_dir}/infer-out/verify.csv", f"{patch_dir}/verify.csv"
    )

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--error_reports", help="error reports")
    parser.add_argument("--patch_id", help="patch_id")
    parser.add_argument("--apply_patch", default=False, action='store_true' ,help="patch_id")
    args=parser.parse_args()
    
    if args.apply_patch:
        patch_dir = f"{ROOT_DIR}/patches/{args.patch_id}"
        with open(f"{patch_dir}/patch.json", "r") as f:
            patch_json = json.load(f)
        source_path_to_patch = f"{ROOT_DIR}/{patch_json['original_filepath']}"
        shutil.copy(f"{patch_dir}/patch.java", f"{source_path_to_patch}")
        shutil.copy(f"{patch_dir}/patch.json", f"{ROOT_DIR}/patch.json")
    
    # elif len(sys.argv) == 3:
    #     verify_patches(sys.argv[1], sys.argv[2], args.error_reports)
    else:
        if os.path.isdir(NPEX_ORIGINAL_SUMMARY_DIR):
            shutil.rmtree(NPEX_ORIGINAL_SUMMARY_DIR)
        shutil.copytree(NPEX_SUMMARY_DIR, NPEX_ORIGINAL_SUMMARY_DIR)
        verify_patches(ROOT_DIR, error_reports=args.error_reports)
