# ITG: Trace Generation via Iterative Interaction between LLM Query and Trace Checking

## Prerequisites

- python>=3.10
- openai==1.2.0
- ltlf2dfa
- tqdm
- argparse
- collections

## Datasets

We use datasets generated by SPOT in our experiments.

Atomic Propositions Numbers: 8

LTL Formula Length: {[5,20),[20-40),[40-60),[60-80),[80-100)}

## Models

We use random/gpt-3.5-turbo/gpt-4 in our experiments.

## Use Examples

### 1. Clone the project and install prerequisites

```cmd
git clone https://github.com/sysulic/ITG.git
cd ITG/src
pip install -r requirements.txt
```

### 2. Set environment variable for openai_api_key

See https://platform.openai.com/docs/quickstart?context=python

### 3. Run python scripts

```cmd
python *.py
```

\* for different methods of our experiments:

- simple_io
- CoT_node
- CoT_tree
- CoT_SC
- Ours

Here are some arguments for choosing different dataset or backend:

```python
'--backend', default='gpt-3.5-turbo', type=str
'--temperature', default=0.0, type=float
'--src', default='../data/little/', type=str
'--file', default='A8_40_60-test.json', type=str
'--s1',default=0,type=int
'--s2',default=100,type=int
'--log', default='test', type=str
'--K', default=4, type=int
'--rpt', default=50, type=int
```

## Citation

Please consider citing the following paper if you find our codes helpful. Thank you!
