import re
import sys
from collections import defaultdict
import logging

logger = logging.getLogger(__name__)

# logging.basicConfig(filename="myapp.log", level=logging.DEBUG)
# logging.basicConfig(level=logging.INFO)
logging.basicConfig(level=logging.DEBUG)
logger.debug("Started")


def remove_comments(text):
    text = re.sub(r"text\s*\\<open>.*?\\<close>", "", text, flags=re.DOTALL)
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.DOTALL)
    return text


def analyze_thy(path):
    with open(path, encoding="utf-8") as f:
        text = f.read()

    text = remove_comments(text)

    # lemma/theorem/corollary で開始する部分から次の lemma/theorem/corollary までで切り出す．
    parts = re.split(r"(?=^\s*(lemma|theorem|corollary)\b)", text, flags=re.MULTILINE)
    # 最初の lemma/theorem/corollary までの部分は削除．
    parts = parts[1:]

    # dict を初期化．
    words_in_proof = {}
    for part in parts:
        m = re.search(r"\b(lemma|theorem|corollary)\s+([A-Za-z0-9_']+)\s*:", part)
        # m = re.search(
        #     r"\b(lemma|theorem|corollary)\s+([A-Za-z0-9_']+)\s*(?:\[[^\]]*\])?\s*:",
        #     part,
        # )
        if m:
            name = m.group(2)
            # logger.debug(f"name: {name}")
            words_in_proof[name] = {"type": m.group(1), "deps": []}
            # logger.debug(f"- {words_in_proof[name]}")
            count = 1
            lines = part.split("\n")
            for line in lines:
                line = line.strip()

                # 証明判定
                if re.search(r"\bproof\b", line):
                    count += 1

                if re.search(r"\bqed\b", line):
                    count -= 1
                    if count == 0:
                        break

                # 証明中
                if count > 0:
                    ws = re.split(r"[^A-Za-z0-9_']+", line)
                    words_in_proof[name]["deps"].extend(ws)

                # “by” が出て count==1 なら即終了
                if count == 1 and re.search(r"\bby\b", line):
                    break
            # print(words_in_proof[name])

    for k in words_in_proof:
        words_in_proof[k]["deps"] = sorted(
            set(
                [x for x in words_in_proof[k]["deps"] if x in words_in_proof and x != k]
            )
        )

    # print(words_in_proof)
    logger.debug(words_in_proof)
    return words_in_proof


def helper(refs, src):
    if not refs[src]["is_marked"]:
        refs[src]["is_marked"] = True
        for target in refs[src]["deps"]:
            helper(refs, target)


def dep_analysis(refs):
    logging.debug("dependency analysis")
    # initialise
    for src, targets in refs.items():
        targets["is_marked"] = False

    for src, targets in refs.items():
        if targets["type"] == "theorem":
            helper(refs, src)
    logging.debug(refs)
    return refs


def refs_to_mermaid(refs):
    """
    refs: {定理名: [参照している定理名…]}
    theorem_names: その .thy に出てくるすべての定理名
    """
    lines = []
    # lines.append("```mermaid")
    lines.append("graph LR")

    # 頂点出力
    for src, targets in refs.items():
        lines.append(f"  {src}:::{targets["type"]}")
        if not targets["is_marked"]:
            lines.append(f"  {src}:::isnotused")

    # エッジ出力
    all_nodes = set(refs.keys())
    for src, targets in refs.items():
        for tgt in targets["deps"]:
            lines.append(f"  {src} --> {tgt}")
            all_nodes.add(src)
            all_nodes.add(tgt)

    # # エッジを持たない（孤立）ノードも一応宣言しておく
    # for name in sorted(all_nodes):
    #     # 既にエッジのどこかに出ていれば明示不要だが、
    #     # 冗長でも害はないのでそのまま出してもよい。
    #     # ここでは「エッジに一度も出てないもの」だけ追加する。
    #     has_edge = any(name in targets["deps"] for src, targets in refs.items())
    #     if not has_edge:
    #         lines.append(f"  {name}")

    lines.append("classDef lemma stroke:#333,fill:#eee")
    lines.append("classDef corollary stroke:#1f1,fill:#dfd")
    lines.append("classDef theorem stroke:#11f,fill:#ddf")
    lines.append("classDef isnotused fill:#f11")
    # lines.append("```")
    return "\n".join(lines)


if __name__ == "__main__":

    if len(sys.argv) != 2:
        print("Usage: python analyze_isabelle.py path/to/file.thy")
        sys.exit(1)

    path = sys.argv[1]

    refs = analyze_thy(path)
    dep_analysis(refs)

    mermaid_str = refs_to_mermaid(refs)
    print(mermaid_str)
