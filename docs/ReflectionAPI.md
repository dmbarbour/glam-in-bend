# Reflection API

The effects reflection tasks may use beyond the standard effects
(Design.md, "Standard Effects"), as the API stands. Reflection APIs may
differ between runtimes (`reflection-api-per-runtime`); this one comes from
the Rust bootstrap, and its terms, such as *machine* for the task a
reflection operation runs in, follow that model until this implementation
revises them. Design.md, "Reflection", covers what reflection is for.

```
.log Severity Message  # emit a diagnostic: 'info, 'warn or 'error; Message is
                       #   normally an object with msg.text (Design.md, "Logging")
.meta.inspect V        # a sealed carrier's metadata, .fail for other values
                       #   (Design.md, "Associated Metadata")
.heap.get Path       # shared heap state; an ERROR at the read where Path
                     #   is undefined
.heap.set Path Value # blind replacement of shared heap state
.heap.rewrite Path F # commit-ordered lazy rewrite of shared heap state
.heap.try_get Path  # the value where defined; .fail where not (also .try_get, .vol.try_get)
.heap.del Path      # removes, pruning what it empties (also .del, .vol.del)
.heap.vol >>= (\h -> .vol.get h Path)  # volume handles: .vol.new/get/set/rewrite
.promise.new >>= (\p -> .promise.fulfill p.resolver 7)  # {promise, resolver}
.promise.status R   # 'pending, 'fulfilled or 'broken, from resolver R
.promise.accept R {msg:{text:"owed"}}  # this machine owes R's promise; .promise.abandon R
.promise.accepted R # unit where any machine accepted it; .fail otherwise
.port.read 'in 2     # the next 2 values as a list; too few is pushback
.port.unread 'in [x] # putback: x stands at the input's head, read next
.port.write 'out [1, 2]  # along every wire from the output; unwired is an ERROR
.port.ask 'q Req     # writes {request, reply}; returns the reply's promise
.port.available 'in  # a count, observed; .port.pending: {port: count}
.wire.add (out:'o) (child:{key:'k, port:'in})  # also .wire.del, .wire.list,
                     #   .wire.defaults 'on/'off; ends in:P, out:P, child:{key, port}
```
