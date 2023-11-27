import openai
from partial_logic_checker import check,ltl2turple
import re
import os
import argparse
import json
import time
from tqdm import tqdm
from collections import Counter
openai.api_key_path="../apikey/oct1.txt"
argparser = argparse.ArgumentParser(description='Select backend, temperature, and dataset.')
argparser.add_argument('--backend', default='gpt-4', type=str)
argparser.add_argument('--temperature', default=0.7, type=float)
argparser.add_argument('--src', default='../data/little/', type=str)
argparser.add_argument('--file', default='A8_60_80-test.json', type=str)
argparser.add_argument('--log', default='test', type=str)
argparser.add_argument('--K', default=4, type=int)
args = argparser.parse_args()
def postorder(ltl,trace,tree,node,res_str):
    elems = tree[node]
    elems = list(elems)
    #print("elems:"+str(elems))
    for elem in elems:
        
        if tree.get(elem) != None:
            postorder(ltl,trace,tree,elem,res_str)
        #print("curr_node:"+str(elem))
        # state a d does not satisfies ltl[b:c]
        if elem[2] == 0:
            res_str+=f"{trace[elem[0]]} not satisfies {''.join(ltl[elem[1][0]:elem[1][1]+1])}."
            #print(f"state {elem[0]} trace {trace[elem[0]]} not satisfies {''.join(ltl[elem[1][0]:elem[1][1]+1])}")
#        else:
#            res_str+=f"trace {trace[elem[0]]} satisfies {''.join(ltl[elem[1][0]:elem[1][1]+1])}."
#            print(f"state {elem[0]} trace {trace[elem[0]]} satisfies {ltl[elem[1][0]:elem[1][1]+1]}")
        #print("tree.get(elem):"+str(tree.get(elem)))
    
        
def flatten(tp):
    i = 0
    while i < len(tp):
        if isinstance(tp[i],tuple):
            tp = tp[:i] + tp[i] + tp[i+1:]
        i+=1
    return tp
# system 

target_description = "Generate a satisfiable trace from input LTL formula. The possible atomic propositions will be given. The possible operators are &, |, !, X, F, G, U. Trace should be less than 10 states. Each state should not contain dublicated atomic propositions. The output trace should be a list of states. Do not use ... in output. For example: LTL: p0 U (X p1) Trace: [[p0],[],[p1]] Proof:{ [[p1]] satisfies p1; [[],[p1]] satisfies X p1 because [[p1]] satisfies p1; [[p0]] satisfies p0; [[p0],[],[p1]] satisfies p0 U (X p1) because [[],[p1]] satisfies X p1 and [[p1]] satisfies p1} FINISH LTL: F(p0 & X p1) Trace: [[p0],[p1]] Proof:{ [[p1]] satisfies p1; [[p0],[p1]] satisfies X p1 because [[p1]] satisfies p1; [[p0],[p1]] satisfies p0; [[p0],[p1]] satisfies p0 & X p1 because [[p0],[p1]] satisfies X p1 and [[p0],[p1]] satisfies p0; [[p0],[p1]] satisfies F(p0 & X p1) because [[p0],[p1]] satisfies p0 & X p1} FINISH LTL: G(p1|!p2) Trace: [[],[p1]] Proof:{ [[p1]] satisfies p1; [[p1]] satisfies p1|!p2 because [[p1]] satisfies p1; [[],[p1]] satisfies !p2; [[],[p1]] satisfies p1|!p2 because [[],[p1]] satisfies !p2; [[],[p1]] satisfies G(p1|!p2) because [[p1]] satisfies p1|!p2 and [[],[p1]] satisfies p1|!p2} FINISH"


# each state should only contain the atomic propositions that appears in the formula
LTLs = []
ltl_source = args.src+args.file

print(f"ltl_source:{ltl_source}")
with open(ltl_source, "r") as f:
    #read json file
    ltl_data = json.load(f)
    #print(len(ltl_data))
    for ltl in ltl_data:
        if ltl["issat"] == True:
            LTLs.append(ltl["inorder"])

# print(len(LTLs))
# print(LTLs[0])
# user

print("Welcome to the LTL satisfiability prediction system. We have "+str(len(LTLs))+" LTL formulas to predict.")
init_message = [{"role":"system","content":target_description}]
count = 0
K = args.K
ltl_size = len(LTLs)
total_time = 0
each_count = []
test_example = 3
for ltl in tqdm(LTLs,desc="check"):

    #print(f"count:{count}")
    #print(f"count: {Counter(each_count)}")
    #print("LTL:"+ltl)
    init_message = [{"role":"system","content":target_description}]
    ap = set(re.findall(r'p[0-9]+',ltl))
    #print(ap)
    input_message = ltl + " atomic propositions: " + str(ap)
    init_message.append({"role":"user","content":input_message})
    start_time = time.time()
    try:
        chat = openai.ChatCompletion.create(model="gpt-4", messages=init_message, temperature=0)
    except Exception as e:
        print("error:"+str(e))
        continue
    except KeyboardInterrupt:
        print("quit")
        exit(999)
    end_time = time.time()
    total_time += end_time-start_time
    reply = chat["choices"][0]["message"]["content"]
    if test_example > 0 :
        print("reply:\n"+reply)
        test_example -= 1
    try:
        trace = reply.split("Trace:")[1]
        trace = trace.split("Proof")[0]
    except:
        trace = reply
    
    
    #ctn = input("press any key to continue")

    try:
        trace = eval(trace)
    except:
        try:
            trace = re.sub(r'(p[0-9]+)',r"'\1'",trace)
            trace = eval(trace)
        except:
            print("trace error")
            continue
    
    if len(trace) <=1 :
        trace.append(trace[0])
    vocab = ap
    ltl_test = re.sub(r'(?<![p0-9])[0]','FALSE',ltl)
    ltl_test = re.sub(r'(?<![p0-9])[1]','TRUE',ltl_test)
    for i in range(len(trace)):
        test_trace = (trace, i)    
        res_test,proof_dic,root_node = check(ltl_test, test_trace, vocab)
        #print(f"check result:{bool(res_test)}")
        if res_test == True:
            count+=1
            break
    
    
end_time = time.time()
print(f"count:{count}")
print(f"semantic acc: {count/len(LTLs)}")
print(f"time: {total_time}")