
from copy import deepcopy
import sys
from ltlf2dfa.parser.ltlf import LTLfParser, LTLfAnd, LTLfUntil, LTLfNot, LTLfAlways, LTLfAtomic, LTLfNext, LTLfOr, LTLfEventually, LTLfImplies, LTLfRelease

sys.setrecursionlimit(100000)
# 三个&的时候这个生成的是& a & b c
proof=''
proofcnt=0
printproof=False
len_cache={}
switch_cnt = [0] * 100
# change1: f_wait 在当前状态之前已经要求检查的cache
# change2:
# 新增输出证明树，证明节点需要 (t时刻，(a,b)公式区间，1或0期望的满足性)
# 所以输入时增加输入当前公式起点位置a ，b可以计算得到（目前直接简单转成str算），期望值
# 返回值多一个证明节点
# 递归时，根据递归来的值是否与期望一样决定是否将 str(当前节点):子节点搞进去
def formula_len(f,cache):
    # print('f',f)
    if cache.get(f,-1)!=-1:
        return cache[f]
    if isinstance(f,str):
        cache[f] = 1
        return 1
    else:
        cnt=0
        for i in f:
            cnt+=formula_len(i,cache)
        cache[f]=cnt
        return cnt

def get_switch_cnt():
    global switch_cnt
    return switch_cnt

def checkLTL(f, f_wait, t, trace, loop_start, vocab, c={}, v=False, formula_start=0, expect_val=1, proof_dic={}):
    """ Checks satisfaction of a LTL formula on an execution trace

        NOTES:
        * This works by using the semantics of LTL and forward progression through recursion
        * Note that this does NOT require using any off-the-shelf planner

        ARGUMENTS:
            f       - an LTL formula (must be in TREE format using nested tuples
                      if you are using LTL dict, then use ltl['str_tree'])
            t       - time stamp where formula f is evaluated
            trace   - execution trace (a dict containing:
                        trace['name']:    trace name (have to be unique if calling from a set of traces)
                        trace['trace']:   execution trace (in propositions format)
                        trace['plan']:    plan that generated the trace (unneeded)
            vocab   - vocabulary of propositions
            c       - cache for checking LTL on subtrees
            v       - verbosity

        OUTPUT:
            satisfaction  - true/false indicating ltl satisfaction on the given trace
    """
    global len_cache
    global switch_cnt
    # change
    if t==len(trace['trace']):#循环
        if loop_start==-1:
            return (expect_val,(t,(formula_start,formula_start+formula_len(f,len_cache)-1),expect_val))
        else:
            t=loop_start

    #当前的证明树节点
    proof_node=(t,(formula_start,formula_start+formula_len(f,len_cache)-1),expect_val)
    sub_node_list=[]
    sub_node_mode='or'  # 默认就or

    if v:
        print('\nCurrent t = ' + str(t))
        print('Current f =', f)
    # if printproof:
    #     print(proofcnt,':'+str(t)+':'+str(trace['trace'][t])+':'+str(f)+'\n')
    ###################################################

    # Check if first operator is a proposition
    if type(f) is str and f in vocab:
        # proofcnt-=1
        switch_cnt[0]+=1
        return (f in trace['trace'][t], proof_node)
    #change: 现在公式里还有0，1
    if type(f) is str and f=='0':
        switch_cnt[0] += 1
        # proofcnt-=1
        return (False, proof_node)
    if type(f) is str and f=='1':
        switch_cnt[0] += 1
        # proofcnt-=1
        return (True, proof_node)

    # Check if sub-tree info is available in the cache
    key = (f, t, trace['name'])
    if c is not None:
        if key in c:
            if v: print('Found subtree history')
            # proofcnt-=1
            return (c[key],proof_node)
    # change 用这个避免无限递归
    if key in f_wait:
        f_wait[key]+=1
    else:
        f_wait[key]=1

    # Check for standard logic operators
    # 语义一样不需要改
    f0case=0
    if f[0] in ['not', '!']:
        value,sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v, formula_start+1, 1-expect_val, proof_dic)
        value = not value
        sub_node_list.append(sub_node)
        f0case=1
    elif f[0] in ['and', '&', '&&']:
        sub_node_mode='and'
        cnt=1
        value = True
        for i in range(1,len(f)):
            value,sub_node=checkLTL(f[i], f_wait, t, trace, loop_start, vocab, c, v, formula_start+cnt, expect_val, proof_dic)
            cnt+=formula_len(f[i],len_cache) #记下前面的公式占多长
            sub_node_list.append(sub_node)
            if value is False:
                break
        f0case=2
        #
        # value = all((checkLTL(f[i], f_wait, t, trace, loop_start, vocab, c, v) for i in range(1, len(f))))
    elif f[0] in ['or', '||','|']:
        cnt = 1
        value = False
        for i in range(1,len(f)):
            value,sub_node=checkLTL(f[i], f_wait, t, trace, loop_start, vocab, c, v, formula_start+cnt, expect_val, proof_dic)
            cnt+=formula_len(f[i],len_cache) #记下前面的公式占多长
            sub_node_list.append(sub_node)
            if value is True:
                break
        f0case=3
        # value = any((checkLTL(f[i], f_wait, t, trace, loop_start, vocab, c, v) for i in range(1, len(f))))
    elif f[0] in ['imp', '->']:

        value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v, formula_start + 1, 1 - expect_val, proof_dic)
        value = not value
        sub_node_list.append(sub_node)
        if value is False: # 一个为真就够了
            value, sub_node = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v, formula_start+1+formula_len(f[1],len_cache), proof_dic)
            sub_node_list.append(sub_node)
        switch_cnt[4] += 1
        # value = not (checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v)) or checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v)

    # change:原来这里是到了最后一个时刻进入该分支，现在改为已经有同样的调用待返回时进入该递归
    elif f_wait[key]>1: #这个已经待证明了  #这里面的都是证明到最后时刻了，所以只要
        # Confirm what your interpretation for this should be.
        if f[0] in ['G', 'F']:
            value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v, formula_start+1, expect_val, proof_dic)  # Confirm what your interpretation here should be
            sub_node_list.append(sub_node)
            f0case=5
            if f[0]=='F':
                f0case = 6
        elif f[0] == 'U':
            # 检查 p U q，到最后时刻q还不出现则肯定没出现了，所以只要检查q
            value, sub_node = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v, formula_start+1+formula_len(f[1],len_cache), expect_val, proof_dic)
            sub_node_list.append(sub_node)
            f0case=7
        elif f[0] == 'W':  # weak-until
            # p W q, q可以不出现，只要p一直成立
            value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v, formula_start + 1, 1 - expect_val, proof_dic)
            sub_node_list.append(sub_node)
            if value is False:  # 一个为真就够了
                value, sub_node = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v,
                                             formula_start + 1 + formula_len(f[1], len_cache), proof_dic)
                sub_node_list.append(sub_node)

        elif f[0] == 'R':  # release (weak by default)
            # p R q，q一直为真或者有个状态 p&q为真 所以也不用改

            value, sub_node = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v,
                                         formula_start + 1 + formula_len(f[1],len_cache), expect_val, proof_dic)
            sub_node_list.append(sub_node)
            f0case=8
            # value = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v)
        elif f[0] == 'X':
            value, sub_node = checkLTL(f[1], f_wait, t+1, trace, loop_start, vocab, c, v, formula_start + 1, expect_val, proof_dic)
            sub_node_list.append(sub_node)
            f0case=9

        # change:没有weak next
        else:
            return (False,proof_node)
            # Does not exist in vocab, nor any of operators
            print(f,t,vocab)
            sys.exit('LTL check - something wrong')

    else:
        # Forward progression rules
        if f[0] == 'X':  # change:删去了N
            # value = checkLTL(f[1], f_wait, t + 1, trace, loop_start, vocab, c, v)
            value, sub_node = checkLTL(f[1], f_wait, t + 1, trace, loop_start, vocab, c, v, formula_start + 1,
                                       expect_val, proof_dic)
            sub_node_list.append(sub_node)
            f0case=10
        elif f[0] == 'G':
            sub_node_mode = 'and'
            value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v, formula_start + 1,
                                       expect_val, proof_dic)
            sub_node_list.append(sub_node)
            if value is True:
                value, sub_node = checkLTL(f, f_wait, t + 1, trace, loop_start, vocab, c, v, formula_start, expect_val, proof_dic)
                sub_node_list.append(sub_node)
            f0case = 11
        elif f[0] == 'F':
            value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v, formula_start + 1,
                                       expect_val, proof_dic)
            sub_node_list.append(sub_node)
            if value is False:
                value, sub_node = checkLTL(f, f_wait, t + 1, trace, loop_start, vocab, c, v, formula_start, expect_val, proof_dic)
                sub_node_list.append(sub_node)
            f0case = 12
            # value = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v) or checkLTL(('F', f[1]), f_wait, t + 1, trace, loop_start, vocab, c, v)
        elif f[0] == 'U' or f[0]=='W':
            # Basically enforces f[1] has to occur for f[1] U f[2] to be valid.
            value, sub_node = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v,
                                         formula_start + 1 + formula_len(f[1],len_cache), expect_val, proof_dic)
            sub_node_list.append(sub_node)
            if value is False:
                if expect_val == True: #期待为真的话，要两个都加入list
                    sub_node_list=[]
                    sub_node_mode='and'
                value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v,
                                           formula_start + 1, expect_val, proof_dic)
                sub_node_list.append(sub_node)
                if value is True:
                    value, sub_node = checkLTL(f, f_wait, t+1, trace, loop_start, vocab, c, v,
                                               formula_start, expect_val, proof_dic)
                    if expect_val == False: #期待为假的话，只要一个
                        sub_node_list[-1]=sub_node
                    else:
                        sub_node_list.append(sub_node)

            f0case = 13
            # value = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v) or (
            #             checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v) and checkLTL(('U', f[1], f[2]), f_wait, t + 1, trace, loop_start, vocab,
            #                                                                c, v))

        # elif f[0] == 'W':  # weak-until
            # value = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v) or (
            #             checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v) and checkLTL(('W', f[1], f[2]), f_wait, t + 1, trace, loop_start, vocab, c,
            #                                                                v))
        elif f[0] == 'R':  # release (weak by default)

            sub_node_mode = 'and'
            value, sub_node = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v,
                                         formula_start + 1 + formula_len(f[1],len_cache), expect_val, proof_dic)
            sub_node_list.append(sub_node)
            f0case = 14
            if value == True:
                if expect_val == False: #期待为假的话，前面那个就不需要了
                    sub_node_list=[]
                    sub_node_mode='or'
                value, sub_node = checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v,
                                           formula_start + 1, expect_val, proof_dic)
                sub_node_list.append(sub_node)
                if value == False:
                    value, sub_node = checkLTL(f, f_wait, t+1, trace, loop_start, vocab, c, v,
                                               formula_start, expect_val, proof_dic)
                    if expect_val == True: #期待为真那前面false的就不用了
                        sub_node_list[-1]=sub_node
                    else:
                        sub_node_list.append(sub_node)

            # value = checkLTL(f[2], f_wait, t, trace, loop_start, vocab, c, v) and (
            #             checkLTL(f[1], f_wait, t, trace, loop_start, vocab, c, v) or checkLTL(('R', f[1], f[2]), f_wait, t + 1, trace, loop_start, vocab, c, v))
        else:
            return (False,proof_node)
            # Does not exist in vocab, nor any of operators
            print(f, t, vocab)
            sys.exit('LTL check - something wrong')

    if v: print('Returned: ' + str(value))

    if expect_val == value:#这个需求跟实际一样，说明子节点肯定也满足了需要，可以作为证明树
        if expect_val == False: #需求为假而且是and关系，那肯定是最后一个False
            if sub_node_mode == 'and':
                sub_node_list = sub_node_list[-1:]
        if expect_val == True:
            if sub_node_mode == 'or':
                sub_node_list = sub_node_list[-1:]

        cof=len(sub_node_list)
        switch_cnt[cof*15-15+f0case]+=1
        # if f[0] == 'U':
        #     print('pre-curnode:', proof_node, sub_node_list)
        if proof_dic.get(proof_node,-1)!=-1:
            a=set(sub_node_list)
            a=a.union(proof_dic[proof_node])
            proof_dic[proof_node]=a
        else:
            proof_dic[proof_node]=set(sub_node_list)
        if proof_node in proof_dic[proof_node]:
            proof_dic[proof_node].remove(proof_node)
        # if f[0] == 'U':
        #     print('after-curnode:', proof_node, proof_dic[proof_node])
    # Save result
    if c is not None and type(c) is dict:
        key = (f, t, trace['name'])
        c[key] = value  # append

    if printproof:
        print('state:'+str(t) + ':' + str(trace['trace'][t]) + ', sub formula:' + str(f) + 'is '+ str(value))
    # proofcnt -= 1
    return (value,proof_node)


# 将输入的原始ltl公式转换成前缀元组
def preorder_turple(f):
    if isinstance(f, LTLfAtomic):
        return f.s.replace('true', '1').replace('false', '0')
    if isinstance(f, LTLfAnd) or isinstance(f, LTLfUntil) or isinstance(f, LTLfOr) or isinstance(f, LTLfRelease) or isinstance(f, LTLfImplies):
        if len(f.formulas)>2:
            nf=deepcopy(f)
            nf.formulas=nf.formulas[1:]
            return (f.operator_symbol,preorder_turple(f.formulas[0]),preorder_turple(nf))
        return tuple([f.operator_symbol.replace('R', 'W')]+[preorder_turple(f.formulas[i]) for i in range(len(f.formulas))])
    if isinstance(f, LTLfNot) or isinstance(f, LTLfNext) or isinstance(f, LTLfAlways) or isinstance(f, LTLfEventually):
        return (f.operator_symbol,preorder_turple(f.f))

def ltl2turple(ltl: str):
    # print('ltl',ltl)
    parser = LTLfParser()
    formula = parser(ltl)
    return preorder_turple(formula)


def check(ltl,trace,vocab):
    t,loop_start=trace
    trace={'name':'t','trace':t}
    formula=ltl2turple(ltl)
    if printproof:
        print('formula',formula)
    # print(ltl2prefix(ltl))
        print('trace',t)
        print('loop_start',loop_start)
    proof_dic={}
    value,root_node=checkLTL(formula, {}, 0, trace, loop_start, vocab, {}, False, 0, 1, proof_dic)

    return value,proof_dic,root_node

if __name__ == '__main__':

    ltl='p0 U p1'
    trace=([['p0'], ['p3','p2']],-1)
    vocab={f'p{i}' for i in range(10)}
    value=check(ltl,trace,vocab)
    print('value',value)