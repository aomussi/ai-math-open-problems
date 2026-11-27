"""Check complete winning-strategy trees encoded by their root-to-leaf move words.
Each character is a move 3 or 5; odd-numbered moves are by Player I.
No game solver or conjectural result is used here.
"""
import json
from pathlib import Path

certificates=json.loads(Path(__file__).with_name('exception_strategy_words.json').read_text())
for key,words in certificates.items():
    n=int(key)
    assert len(words)==len(set(words))
    assert all(set(word)<={'3','5'} for word in words)
    node_count=0
    def check(prefix,v,visited):
        global node_count
        node_count+=1
        descendants=[w for w in words if w.startswith(prefix)]
        assert descendants
        legal={str(s) for s in (3,5) if (v+s)%n not in visited}
        if prefix in descendants:
            assert descendants==[prefix]
            assert not legal and len(prefix)%2==1
            return
        offered={w[len(prefix)] for w in descendants}
        if len(prefix)%2==0:  # Player I follows one specified legal move.
            assert len(offered)==1 and offered<=legal
        else:  # Every legal response by Player II is covered.
            assert offered==legal
        for s in offered:
            dest=(v+int(s))%n
            check(prefix+s,dest,visited|{dest})
    check('',0,{0})
    print(f'n={n}: first-player win verified, {len(words)} leaves, {node_count} nodes')
