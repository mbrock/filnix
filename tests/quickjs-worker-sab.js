// One module serves as both parent and worker. Exercise sharing, rather
// than merely checking that an echoed copy contains the right bytes.
import * as os from "os";
import * as std from "std";

function check(got, want) {
  if (got !== want) throw new Error(`${got} !== ${want}`);
}

if (os.Worker.parent) {
  const parent = os.Worker.parent;
  let saved;
  parent.onmessage = ({data}) => {
    switch (data.type) {
    case "share":
      check(data.self, data);
      check(data.a, data.alias);
      check(data.view, data.viewAlias);
      check(data.view.buffer, data.a);
      check(data.view.byteOffset, 5);
      check(data.view.length, 9);
      check(data.empty.byteLength, 0);
      check(data.view[0], 17);
      check(data.view[8], 29);
      check(Atomics.add(data.ints, 1, 7), -13);
      data.view[0] = 61;
      data.view[8] = 93;
      saved = data;
      parent.postMessage({type: "shared", a: data.a, alias: data.a,
                          ints: data.ints});
      break;
    case "confirm":
      // The original received message and its pointer table are gone.
      std.gc();
      check(saved.view[4], 84);
      check(Atomics.load(saved.ints, 2), 12345);
      saved = null;
      parent.postMessage({type: "confirmed"});
      break;
    case "queued":
      check(data.a, data.alias);
      check(new Uint8Array(data.a)[3], data.id + 11);
      parent.postMessage({type: "queued_done", id: data.id, a: data.a});
      break;
    case "stop":
      parent.postMessage({type: "done"});
      parent.onmessage = null;
      break;
    default:
      throw new Error("unexpected worker message");
    }
  };
} else {
  const worker = new os.Worker("./quickjs-worker-sab.js");
  const a = new SharedArrayBuffer(37);
  const ints = new Int32Array(new SharedArrayBuffer(12));
  const view = new Uint8Array(a, 5, 9);
  view[0] = 17;
  view[8] = 29;
  ints[1] = -13;
  let message = {type: "share", a, alias: a, view, viewAlias: view, ints,
                 empty: new SharedArrayBuffer(0)};
  message.self = message;
  let next = 0;
  const timer = os.setTimeout(() => {
    console.log("quickjs worker SAB timeout");
    std.exit(1);
  }, 30000);
  worker.onmessage = ({data}) => {
    switch (data.type) {
    case "shared":
      check(data.a, data.alias);
      check(data.a === a, false); // New JS wrapper, same backing store.
      check(view[0], 61);
      check(view[8], 93);
      check(Atomics.load(ints, 1), -6);
      view[4] = 84;
      Atomics.store(ints, 2, 12345);
      worker.postMessage({type: "confirm"});
      break;
    case "confirmed":
      // Drop sender wrappers after enqueueing; queue references must keep
      // the backing stores alive, including messages not yet received.
      for (let id = 0; id < 32; id++) {
        let buffer = new SharedArrayBuffer(id + 8);
        new Uint8Array(buffer)[3] = id + 11;
        worker.postMessage({type: "queued", id, a: buffer, alias: buffer});
      }
      std.gc();
      break;
    case "queued_done":
      check(data.id, next++);
      check(data.a.byteLength, data.id + 8);
      check(new Uint8Array(data.a)[3], data.id + 11);
      if (next === 32) worker.postMessage({type: "stop"});
      break;
    case "done":
      check(next, 32);
      worker.onmessage = null;
      os.clearTimeout(timer);
      console.log("quickjs worker SAB ok");
      break;
    default:
      throw new Error("unexpected parent message");
    }
  };
  worker.postMessage(message);
  message = null;
  std.gc();
}
