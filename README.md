# TODO

LTL 的 翻译/SATUNSAT二分类/迹生成

randltl -n 10 a b c d e --ltl-priorities 'xor=0,implies=0,equiv=0,W=0,M=0,R=0'

1. 输入任务：Your target is to predict the following LTL sentence is satisfiable or not. Here, the LTL sentence is given as a string. LTL will not stay at any state. You do not need further information. And if exists a trace that satisfies LTL sentence, we say it is satisfiable. You do not need to consider its counterexample.
2. 加入环的遍历，即不断假设环的出现位置，直到sat或者循环结束
