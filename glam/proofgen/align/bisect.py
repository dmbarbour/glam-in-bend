# glam/proofgen (an authoring aid): check ALIGN.bend's defs as growing prefixes, naming the
# first whose prefix fails (Bend reports a stack overflow with no place)
import os, re, subprocess, sys
D=os.path.dirname(os.path.abspath(__file__))+'/'
ROOT=os.path.dirname(os.path.dirname(os.path.dirname(D.rstrip('/'))))
src=open(D+'ALIGN.bend').read()
starts=[m.start() for m in re.finditer(r'(?m)^def ', src)]
names=[re.match(r'def ([\w.]+)', src[i:]).group(1) for i in starts]
lo=int(sys.argv[1]) if len(sys.argv)>1 else 0
for k in range(lo, len(starts)):
    end=starts[k+1] if k+1<len(starts) else len(src)
    body=src[:end]
    if 'def main(' not in body: body+='\ndef main() -> U32:\n  0\n'
    open(D+'ALIGN_cut.bend','w').write(body)
    r=subprocess.run([ROOT+'/scripts/capped.sh','3000','300','bend',D+'ALIGN_cut.bend'],capture_output=True,text=True,cwd=D)
    out=(r.stdout+r.stderr)
    ok='FAIL' not in out and 'rror' not in out
    print(names[k], 'ok' if ok else 'FAILS'); sys.stdout.flush()
    if not ok:
        print('\n'.join(l for l in out.split('\n') if l.strip())[:1500]); break
