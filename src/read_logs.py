import os
import argparse
import re

argparser = argparse.ArgumentParser(description='Select backend, temperature, and dataset.')
argparser.add_argument('--backend', default='gpt35', type=str)
argparser.add_argument('--temperature', default=0.0, type=float)
argparser.add_argument('--src', default='../data/little/', type=str)
argparser.add_argument('--file', default='A8_20_40-test.json', type=str)
argparser.add_argument('--s1',default=100,type=int)
argparser.add_argument('--s2',default=1000,type=int)
argparser.add_argument('--log', default='./logs/', type=str)
# read count in the log file
def read_file(log_file):
    count = 0
    ttime = 0
    with open(log_file, "r") as f:
        for line in f:
            if "count:" in line:
                count = int(re.findall(r'\d+', line)[0])
            if "time" in line:
                ttime = float(re.findall(r'\d+\.\d+', line)[0])
    return count,ttime

def main():
    # open log file with correct name
    args = argparser.parse_args()
    file_name = args.file
    backend = args.backend
    s1 = args.s1
    s2 = args.s2
    # find all txt files in the log folder
    log_files = os.listdir(args.log)
    #print(log_files)
    # find the log file with correct name
    logs2read = []
    for file in log_files:
        if file_name in file and backend in file:
            logs2read.append(file)
    print(len(logs2read))
    tot_count = 0
    tot_time = 0
    ltl_size = 0
    for file in logs2read:
        #s1 = int(file.split("s1")[1].split("s2")[0])
        #s2 = int(file.split("s2")[1].split(".txt")[0])
        #ltl_size += s2-s1
        log_file = args.log+file
        count,ttime = read_file(log_file)
        tot_count+=count
        tot_time+=ttime
        #print(f"{log_file} count:{count}")
    ltl_size = 900
    print(f"total count:{tot_count}")
    print(f"accuracy:{tot_count/ltl_size}")
    print(f"total time:{tot_time} s")

if __name__ == "__main__":
    main()