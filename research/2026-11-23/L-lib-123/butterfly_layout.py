"""Check the split butterfly model and exact path loads at specified finite widths."""
from collections import Counter

def make_layout(k):
    m=1<<k
    def incoming(i,w):
        return (2*i)*m+w
    def outgoing(i,w):
        return (2*i+1)*m+(m-1-w)
    pages=[[] for _ in range(4)]
    for i in range(k+1):
        for w in range(m):
            pages[0].append((incoming(i,w),outgoing(i,w)))
            if i<k:
                pages[1].append((outgoing(i,w),incoming(i+1,w)))
                pages[2+((w>>i)&1)].append((outgoing(i,w),incoming(i+1,w^(1<<i))))
    return m, incoming, outgoing, pages

def check(k):
    m, incoming, outgoing, pages=make_layout(k)
    for page in pages:
        events={}
        for a,b in page:
            assert a<b and a not in events and b not in events
            events[a]=(True,b)
            events[b]=(False,b)
        stack=[]
        for pos in sorted(events):
            op,b=events[pos]
            if op:
                stack.append(b)
            else:
                assert stack and stack.pop()==b
        assert not stack
    edges={edge for page in pages for edge in page}
    seen=Counter()
    for a in range(m):
        for b in range(m):
            path=[]
            for j in range(k+1):
                mask=(1<<j)-1
                w=(a&~mask)|(b&mask)
                path.extend((incoming(j,w),outgoing(j,w)))
            assert all(e in edges for e in zip(path,path[1:]))
            seen.update(path)
    assert len(seen)==2*(k+1)*m
    assert set(seen.values())=={m}
    print(f'k={k}: {len(seen)} vertices, {len(edges)} edges, four valid pages; all vertex loads {m}')

def check_three_pages(k):
    m=1<<k
    layers=[]
    next_pos=0
    for i in range(2*k+1):
        count=m if i%2==0 else m//2
        incoming=range(next_pos,next_pos+count)
        outgoing=range(next_pos+2*count-1,next_pos+count-1,-1)
        layers.append((incoming,outgoing))
        next_pos+=2*count
    pages=[[],[],[]]
    for incoming,outgoing in layers:
        pages[0].extend(zip(incoming,outgoing))
    def delete(x,i):
        return ((x>>(i+1))<<i)|(x&((1<<i)-1))
    for i in range(k):
        for w in range(m):
            group=delete(w,i)
            page=1+((w>>i)&1)
            pages[page].append((layers[2*i][1][w],layers[2*i+1][0][group]))
            pages[page].append((layers[2*i+1][1][group],layers[2*i+2][0][w]))
    for page in pages:
        events={}
        for a,b in page:
            assert a<b and a not in events and b not in events
            events[a]=(True,b)
            events[b]=(False,b)
        stack=[]
        for pos in sorted(events):
            op,b=events[pos]
            if op:
                stack.append(b)
            else:
                assert stack and stack.pop()==b
        assert not stack
    edges={e for page in pages for e in page}
    seen=Counter()
    for a in range(m):
        for b in range(m):
            path=[]
            for j in range(k+1):
                mask=(1<<j)-1
                w=(a&~mask)|(b&mask)
                path.extend((side[w] for side in layers[2*j]))
                if j<k:
                    path.extend((side[delete(w,j)] for side in layers[2*j+1]))
            assert all(e in edges for e in zip(path,path[1:]))
            seen.update(path)
    for j,(incoming,outgoing) in enumerate(layers):
        for vertex in (*incoming,*outgoing):
            assert seen[vertex]==(2*m if j%2 else m)
    print(f'k={k}: {len(seen)} vertices, {len(edges)} edges, three valid pages; load at most {2*m}')

if __name__=='__main__':
    for k in range(1,9):
        check(k)
        check_three_pages(k)
