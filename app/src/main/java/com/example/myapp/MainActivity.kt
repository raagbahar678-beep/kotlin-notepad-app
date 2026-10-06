package com.example.myapp

import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.pm.ServiceInfo
import android.graphics.PixelFormat
import android.os.Build
import android.os.IBinder
import android.provider.Settings
import android.view.PointerIcon
import android.view.WindowManager
import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.net.Uri
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.text.InputType
import android.view.GestureDetector
import android.view.Gravity
import android.view.KeyCharacterMap
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.ScaleGestureDetector
import android.view.View
import android.view.ViewGroup
import android.view.inputmethod.BaseInputConnection
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.InputConnection
import android.view.inputmethod.InputMethodManager
import android.widget.Button
import android.widget.CheckBox
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.OverScroller
import android.widget.RadioButton
import android.widget.RadioGroup
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.BufferedWriter
import java.io.Closeable
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.IOException
import java.io.OutputStream
import java.io.OutputStreamWriter
import java.io.RandomAccessFile
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.util.regex.Matcher
import java.util.regex.Pattern

// ═══════════════════════════ globals / helpers ═══════════════════════════
var gDensity: Float = 1f
fun dp(v: Int): Int = (v * gDensity + 0.5f).toInt()
fun dpf(v: Float): Float = v * gDensity

const val STRIDE = 128
const val MAX_BLOCK_BYTES = 32 * 1024 * 1024
const val INLINE_CHUNK = 4096

val MARK_COLOURS: IntArray = intArrayOf(
    0xFFFF6666.toInt(), 0xFFFFCC44.toInt(), 0xFF66FF99.toInt(),
    0xFF66CCFF.toInt(), 0xFFCC88FF.toInt(), 0xFFFF9944.toInt())

fun fmtSize(b: Long): String {
    if (b < 1024L) return "$b B"
    val kb = b / 1024.0
    if (kb < 1024.0) return String.format("%.1f KB", kb)
    val mb = kb / 1024.0
    if (mb < 1024.0) return String.format("%.1f MB", mb)
    return String.format("%.2f GB", mb / 1024.0)
}

// ═══════════════════════════ random-access source ═══════════════════════════
class Src(val ch: FileChannel, val closer: Closeable, val size: Long) {
    fun readInto(pos: Long, buf: ByteArray, off: Int, len: Int): Int {
        val bb = ByteBuffer.wrap(buf, off, len)
        var p = pos
        var total = 0
        while (total < len) {
            val n = ch.read(bb, p)
            if (n <= 0) break
            total += n
            p += n.toLong()
        }
        return total
    }
    fun read(pos: Long, len: Int): ByteArray {
        val buf = ByteArray(len)
        val n = readInto(pos, buf, 0, len)
        return if (n == len) buf else buf.copyOf(n)
    }
    fun close() {
        try { closer.close() } catch (e: Exception) { }
    }
}

fun openUriSrc(ctx: Context, uri: Uri): Src {
    val pfd = ctx.contentResolver.openFileDescriptor(uri, "r") ?: throw IOException("Cannot open file")
    val fis = FileInputStream(pfd.fileDescriptor)
    val ch = fis.channel
    val st = pfd.statSize
    val sz: Long = if (st >= 0L) st else ch.size()
    val cl = object : Closeable {
        override fun close() {
            try { fis.close() } catch (e: Exception) { }
            try { pfd.close() } catch (e: Exception) { }
        }
    }
    return Src(ch, cl, sz)
}

fun openFileSrc(f: File): Src {
    val raf = RandomAccessFile(f, "r")
    return Src(raf.channel, raf, raf.length())
}

// ═══════════════════════════ piece table ═══════════════════════════
class Piece(val lines: Array<String>?, val start: Int, val count: Int)
class Snap(val pieces: Array<Piece>, val cl: Int, val cc: Int)
class DState(val pieces: Array<Piece>, val cum: IntArray, val total: Int)

class Doc {
    var src: Src? = null
    var srcKind: String = "none"      // "uri" | "file" | "none"
    var srcRef: String = ""
    var target: Uri? = null
    @Volatile var eol: String = "\n"
    var idx: LongArray = LongArray(1024)
    @Volatile var idxN: Int = 0
    @Volatile var baseLines: Int = 1
    @Volatile var knownEnd: Long = 0L
    @Volatile var indexing: Boolean = false
    @Volatile var indexedBytes: Long = 0L
    @Volatile var cancel: Boolean = false
    var truncatedIndex: Boolean = false
    @Volatile var st: DState = DState(arrayOf(Piece(arrayOf(""), 0, 1)), intArrayOf(0, 1), 1)
    var version: Int = 0
    var modified: Boolean = false
    val undo = ArrayList<Snap>()
    val redo = ArrayList<Snap>()
    var lastEditKey: String? = null
    var lastEditTime: Long = 0L
    private val cache = LinkedHashMap<Int, Array<String>>(64, 0.75f, true)
    private var cacheChars: Long = 0L
    var progress: Runnable? = null
    var afterIndex: (() -> Unit)? = null
    var pieceJson: JSONArray? = null
    var pieceJsonVer: Int = -1

    val total: Int get() = st.total

    // ── state ──
    fun setStateArr(arr: Array<Piece>) {
        val c = IntArray(arr.size + 1)
        var t = 0
        for (i in arr.indices) { c[i] = t; t += arr[i].count }
        c[arr.size] = t
        st = DState(arr, c, t)
    }

    fun normalize(list: List<Piece>): ArrayList<Piece> {
        val out = ArrayList<Piece>()
        for (p in list) {
            if (p.count <= 0) continue
            if (out.isNotEmpty()) {
                val q = out[out.size - 1]
                val ql = q.lines
                val pl = p.lines
                if (ql == null && pl == null && q.start + q.count == p.start) {
                    out[out.size - 1] = Piece(null, q.start, q.count + p.count)
                    continue
                }
                if (ql != null && pl != null && ql.size + pl.size <= INLINE_CHUNK) {
                    out[out.size - 1] = Piece(ql + pl, 0, ql.size + pl.size)
                    continue
                }
            }
            out.add(p)
        }
        if (out.isEmpty()) out.add(Piece(arrayOf(""), 0, 1))
        return out
    }

    fun setState(list: List<Piece>) {
        setStateArr(normalize(list).toTypedArray())
    }

    fun sub(from: Int, to: Int): ArrayList<Piece> {
        val s = st
        val out = ArrayList<Piece>()
        for (i in s.pieces.indices) {
            val g = s.cum[i]
            val p = s.pieces[i]
            val lo = maxOf(from, g)
            val hi = minOf(to, g + p.count)
            if (hi <= lo) continue
            if (lo == g && hi == g + p.count) { out.add(p); continue }
            val il = p.lines
            if (il != null) out.add(Piece(il.copyOfRange(lo - g, hi - g), 0, hi - lo))
            else out.add(Piece(null, p.start + (lo - g), hi - lo))
        }
        return out
    }

    fun addInline(list: ArrayList<Piece>, lines: Array<String>) {
        var i = 0
        while (i < lines.size) {
            val e = minOf(lines.size, i + INLINE_CHUNK)
            list.add(Piece(lines.copyOfRange(i, e), 0, e - i))
            i = e
        }
    }

    private fun pushUndo(curL: Int, curC: Int, key: String?) {
        val now = System.currentTimeMillis()
        val coalesce = key != null && key == lastEditKey && now - lastEditTime < 1200L && undo.isNotEmpty()
        if (!coalesce) {
            undo.add(Snap(st.pieces, curL, curC))
            if (undo.size > 400) undo.removeAt(0)
        }
        lastEditKey = key
        lastEditTime = now
        redo.clear()
    }

    /** replace logical lines [a, bEx) with newLines */
    fun edit(a: Int, bEx: Int, newLines: Array<String>, curL: Int, curC: Int, key: String?) {
        pushUndo(curL, curC, key)
        val list = ArrayList<Piece>()
        list.addAll(sub(0, a))
        addInline(list, newLines)
        list.addAll(sub(bEx, st.total))
        setState(list)
        modified = true
        version++
    }

    /** delete inclusive line ranges (sorted/merged here). Tk-like: if the last line is included an empty line remains. */
    fun deleteRanges(ranges: List<IntArray>, curL: Int, curC: Int) {
        if (ranges.isEmpty()) return
        val rs = ArrayList<IntArray>()
        for (r in ranges) rs.add(intArrayOf(minOf(r[0], r[1]), maxOf(r[0], r[1])))
        rs.sortBy { it[0] }
        val merged = ArrayList<IntArray>()
        for (r in rs) {
            if (merged.isNotEmpty() && r[0] <= merged[merged.size - 1][1] + 1) {
                val m = merged[merged.size - 1]
                if (r[1] > m[1]) m[1] = r[1]
            } else merged.add(intArrayOf(r[0], r[1]))
        }
        pushUndo(curL, curC, null)
        val tot = st.total
        val list = ArrayList<Piece>()
        var pos = 0
        for (r in merged) {
            val a = maxOf(0, r[0])
            val b = minOf(tot - 1, r[1])
            if (b < a) continue
            if (a > pos) list.addAll(sub(pos, a))
            pos = b + 1
        }
        if (pos < tot) list.addAll(sub(pos, tot))
        else list.add(Piece(arrayOf(""), 0, 1))
        setState(list)
        modified = true
        version++
    }

    fun undoOp(curL: Int, curC: Int): Snap? {
        if (undo.isEmpty()) return null
        val sn = undo.removeAt(undo.size - 1)
        redo.add(Snap(st.pieces, curL, curC))
        setStateArr(sn.pieces)
        modified = true
        version++
        lastEditKey = null
        return sn
    }

    fun redoOp(curL: Int, curC: Int): Snap? {
        if (redo.isEmpty()) return null
        val sn = redo.removeAt(redo.size - 1)
        undo.add(Snap(st.pieces, curL, curC))
        setStateArr(sn.pieces)
        modified = true
        version++
        lastEditKey = null
        return sn
    }

    // ── line access ──
    fun getLine(n: Int): String {
        val s = st
        if (n < 0 || n >= s.total) return ""
        var lo = 0
        var hi = s.pieces.size - 1
        while (lo < hi) {
            val mid = (lo + hi + 1) ushr 1
            if (s.cum[mid] <= n) lo = mid else hi = mid - 1
        }
        val p = s.pieces[lo]
        val k = n - s.cum[lo]
        val il = p.lines
        return if (il != null) il[k] else origLine(p.start + k)
    }

    private fun origLine(k: Int): String {
        val b = k / STRIDE
        val arr = blockLines(b)
        val j = k - b * STRIDE
        return if (j < arr.size) arr[j] else ""
    }

    private fun blockLines(b: Int): Array<String> {
        synchronized(cache) {
            val c = cache[b]
            if (c != null) return c
        }
        val arr = loadBlock(b)
        if (indexing && (b.toLong() + 1L) * STRIDE > baseLines.toLong()) return arr
        synchronized(cache) {
            cache[b] = arr
            for (s in arr) cacheChars += (s.length + 8).toLong()
            if (cacheChars > 16000000L) {
                val it = cache.entries.iterator()
                while (cacheChars > 12000000L && cache.size > 1 && it.hasNext()) {
                    val e = it.next()
                    if (e.key == b) continue
                    for (s in e.value) cacheChars -= (s.length + 8).toLong()
                    it.remove()
                }
            }
        }
        return arr
    }

    private fun decode(buf: ByteArray, a: Int, bEx: Int): String {
        var e = bEx
        if (e > a && buf[e - 1] == 13.toByte()) e--
        return String(buf, a, e - a, Charsets.UTF_8)
    }

    private fun loadBlock(b: Int): Array<String> {
        val s = src ?: return arrayOf("")
        val bl = baseLines
        val expected = minOf(STRIDE.toLong(), bl.toLong() - b.toLong() * STRIDE).toInt()
        val ix = idx
        if (expected <= 0) return arrayOf()
        if (b >= idxN) return Array(expected) { "" }
        val off = ix[b]
        val endOff: Long = if (b + 1 < idxN) ix[b + 1] else if (indexing) knownEnd else s.size
        var len = endOff - off
        if (len < 0L) len = 0L
        if (len > MAX_BLOCK_BYTES.toLong()) len = MAX_BLOCK_BYTES.toLong()
        val buf: ByteArray = try { s.read(off, len.toInt()) } catch (e: Exception) { ByteArray(0) }
        val out = ArrayList<String>(expected)
        var st0 = 0
        val n = buf.size
        var i = 0
        while (i < n) {
            if (buf[i] == 10.toByte()) {
                out.add(decode(buf, st0, i))
                st0 = i + 1
                if (out.size == expected) break
            }
            i++
        }
        if (out.size < expected) out.add(decode(buf, st0, n))
        while (out.size < expected) out.add("")
        return out.toTypedArray()
    }

    fun offsetOfLine(k: Int): Long {
        val s = src ?: return 0L
        val b = k / STRIDE
        var off = idx[b]
        var rem = k - b * STRIDE
        if (rem == 0) return off
        val buf = ByteArray(1 shl 16)
        while (rem > 0) {
            val n = s.readInto(off, buf, 0, buf.size)
            if (n <= 0) break
            var i = 0
            while (i < n) {
                if (buf[i] == 10.toByte()) {
                    rem--
                    if (rem == 0) return off + i + 1
                }
                i++
            }
            off += n.toLong()
        }
        return off
    }

    fun getText(l1: Int, c1: Int, l2: Int, c2: Int, maxChars: Int): String? {
        if (l1 == l2) {
            val t = getLine(l1)
            return t.substring(minOf(c1, t.length), minOf(c2, t.length))
        }
        val sb = StringBuilder()
        for (l in l1..l2) {
            val t = getLine(l)
            val a = if (l == l1) minOf(c1, t.length) else 0
            val b = if (l == l2) minOf(c2, t.length) else t.length
            sb.append(t, a, b)
            if (l < l2) sb.append('\n')
            if (sb.length > maxChars) return null
        }
        return sb.toString()
    }

    // ── indexing ──
    private fun addIdx(off: Long) {
        if (idxN >= idx.size) idx = idx.copyOf(idx.size * 2)
        idx[idxN] = off
        idxN = idxN + 1
    }

    private fun refreshPristine(n: Int) {
        setStateArr(arrayOf(Piece(null, 0, maxOf(n, 1))))
    }

    fun beginIndex(ui: Handler, cacheDir: File, lastMod: Long) {
        val s = src ?: return
        var cf: File? = null
        if (s.size >= 64L * 1024L * 1024L) {
            cf = File(cacheDir, "idx_" + (srcRef.hashCode().toLong() and 0xffffffffL) + "_" + s.size + ".bin")
            if (tryLoadCache(cf, s.size, lastMod)) {
                refreshPristine(baseLines)
                ui.post { progress?.run(); afterIndex?.invoke() }
                return
            }
        }
        startIndex(ui, cf, lastMod)
    }

    private fun startIndex(ui: Handler, cf: File?, lastMod: Long) {
        val s = src ?: return
        indexing = true
        cancel = false
        idxN = 0
        baseLines = 0
        knownEnd = 0L
        refreshPristine(0)
        Thread {
            try {
                val buf = ByteArray(4 * 1024 * 1024)
                var pos = 0L
                var nl = 0L
                var lastNlEnd = 0L
                var lastPost = 0L
                var eolSet = false
                addIdx(0L)
                while (!cancel) {
                    val n = s.readInto(pos, buf, 0, buf.size)
                    if (n <= 0) break
                    var i = 0
                    while (i < n) {
                        if (buf[i] == 10.toByte()) {
                            nl++
                            if (!eolSet) {
                                eolSet = true
                                eol = if (i > 0 && buf[i - 1] == 13.toByte()) "\r\n" else "\n"
                            }
                            if (nl % STRIDE.toLong() == 0L) addIdx(pos + i + 1L)
                            lastNlEnd = pos + i + 1L
                        }
                        i++
                    }
                    pos += n.toLong()
                    if (nl >= Int.MAX_VALUE.toLong() - 100000L) { truncatedIndex = true; break }
                    baseLines = nl.toInt()
                    knownEnd = lastNlEnd
                    indexedBytes = pos
                    refreshPristine(baseLines)
                    val now = System.currentTimeMillis()
                    if (now - lastPost > 200L) {
                        lastPost = now
                        ui.post { progress?.run() }
                    }
                }
                if (!cancel) {
                    baseLines = nl.toInt() + 1
                    knownEnd = s.size
                    indexedBytes = s.size
                    refreshPristine(baseLines)
                    if (cf != null) saveCache(cf, s.size, lastMod)
                    indexing = false
                    ui.post { progress?.run(); afterIndex?.invoke() }
                }
            } catch (e: Exception) {
                indexing = false
                ui.post { progress?.run() }
            }
        }.start()
    }

    private fun saveCache(f: File, size: Long, lastMod: Long) {
        try {
            val o = DataOutputStream(BufferedOutputStream(FileOutputStream(f), 1 shl 16))
            o.writeInt(0x4C4E4958)
            o.writeInt(STRIDE)
            o.writeLong(size)
            o.writeLong(lastMod)
            o.writeInt(baseLines)
            o.writeInt(if (eol == "\r\n") 1 else 0)
            o.writeInt(idxN)
            for (i in 0 until idxN) o.writeLong(idx[i])
            o.close()
        } catch (e: Exception) { }
    }

    private fun tryLoadCache(f: File, size: Long, lastMod: Long): Boolean {
        if (!f.exists()) return false
        try {
            val i = DataInputStream(BufferedInputStream(FileInputStream(f), 1 shl 16))
            val ok = i.readInt() == 0x4C4E4958 && i.readInt() == STRIDE && i.readLong() == size && i.readLong() == lastMod
            if (!ok) { i.close(); return false }
            val bl = i.readInt()
            val crlf = i.readInt()
            val n = i.readInt()
            if (n <= 0 || n > 100000000) { i.close(); return false }
            val arr = LongArray(maxOf(n, 1024))
            for (k in 0 until n) arr[k] = i.readLong()
            i.close()
            idx = arr
            idxN = n
            baseLines = bl
            eol = if (crlf == 1) "\r\n" else "\n"
            knownEnd = size
            indexedBytes = size
            indexing = false
            return true
        } catch (e: Exception) {
            return false
        }
    }

    fun close() {
        cancel = true
        src?.close()
    }

    // ── writing ──
    fun hasOrigPieces(): Boolean {
        for (p in st.pieces) if (p.lines == null) return true
        return false
    }

    fun writeAll(out: OutputStream, prog: (Long) -> Unit) {
        val s = st
        val bo = BufferedOutputStream(out, 1 shl 16)
        val eolB = eol.toByteArray(Charsets.UTF_8)
        var written = 0L
        val sr = src
        val buf = ByteArray(1 shl 20)
        for (i in s.pieces.indices) {
            val p = s.pieces[i]
            val last = i == s.pieces.size - 1
            val il = p.lines
            if (il != null) {
                for (j in il.indices) {
                    val bts = il[j].toByteArray(Charsets.UTF_8)
                    bo.write(bts)
                    written += bts.size.toLong()
                    if (!(last && j == il.size - 1)) { bo.write(eolB); written += eolB.size.toLong() }
                }
                prog(written)
            } else if (sr != null) {
                val a = p.start
                val b = p.start + p.count
                val offA = offsetOfLine(a)
                val atEnd = b >= baseLines
                var offB = if (atEnd) sr.size else offsetOfLine(b)
                if (!atEnd && last) {
                    val tail = sr.read(maxOf(offA, offB - 2L), (offB - maxOf(offA, offB - 2L)).toInt())
                    if (tail.isNotEmpty() && tail[tail.size - 1] == 10.toByte()) {
                        offB -= 1L
                        if (tail.size >= 2 && tail[tail.size - 2] == 13.toByte()) offB -= 1L
                    }
                }
                var pos = offA
                while (pos < offB) {
                    val want = minOf(buf.size.toLong(), offB - pos).toInt()
                    val n = sr.readInto(pos, buf, 0, want)
                    if (n <= 0) break
                    bo.write(buf, 0, n)
                    pos += n.toLong()
                    written += n.toLong()
                    prog(written)
                }
                if (atEnd && !last) { bo.write(eolB); written += eolB.size.toLong() }
            }
        }
        bo.flush()
    }

    // ── search ──
    private fun findNonEmpty(m: Matcher, from: Int, len: Int): Boolean {
        var pos = from
        while (pos <= len) {
            if (!m.find(pos)) return false
            if (m.end() > m.start()) return true
            pos = m.end() + 1
        }
        return false
    }

    fun search(pat: Pattern, fl: Int, fc: Int, forward: Boolean, cancelled: () -> Boolean, prog: (Int) -> Unit): IntArray? {
        val tot = st.total
        val m = pat.matcher("")
        var scanned = 0
        if (forward) {
            var l = fl
            var first = true
            while (l < tot) {
                val t = getLine(l)
                m.reset(t)
                val from = if (first) minOf(fc, t.length) else 0
                if (findNonEmpty(m, from, t.length)) return intArrayOf(l, m.start(), m.end())
                first = false
                l++
                scanned++
                if ((scanned and 0x3FFF) == 0) { if (cancelled()) return null; prog(l) }
            }
            l = 0
            while (l <= fl && l < tot) {
                val t = getLine(l)
                m.reset(t)
                if (findNonEmpty(m, 0, t.length)) return intArrayOf(l, m.start(), m.end())
                l++
                scanned++
                if ((scanned and 0x3FFF) == 0) { if (cancelled()) return null }
            }
        } else {
            var l = minOf(fl, tot - 1)
            var first = true
            while (l >= 0) {
                val t = getLine(l)
                m.reset(t)
                val limit = if (first) minOf(fc, t.length) else t.length
                var pos = 0
                var bs = -1
                var be = -1
                while (findNonEmpty(m, pos, t.length)) {
                    if (m.end() > limit) break
                    bs = m.start(); be = m.end(); pos = m.end()
                }
                if (bs >= 0) return intArrayOf(l, bs, be)
                first = false
                l--
                scanned++
                if ((scanned and 0x3FFF) == 0) { if (cancelled()) return null; prog(l) }
            }
            l = tot - 1
            while (l >= fl && l >= 0) {
                val t = getLine(l)
                m.reset(t)
                var pos = 0
                var bs = -1
                var be = -1
                while (findNonEmpty(m, pos, t.length)) { bs = m.start(); be = m.end(); pos = m.end() }
                if (bs >= 0) return intArrayOf(l, bs, be)
                l--
                scanned++
                if ((scanned and 0x3FFF) == 0) { if (cancelled()) return null }
            }
        }
        return null
    }
}

// replacement template (regex mode): \1..\9, \\, \n, \t
class Repl(tmpl: String, regexMode: Boolean) {
    val parts = ArrayList<Any>()
    init {
        if (!regexMode) parts.add(tmpl)
        else {
            val sb = StringBuilder()
            var i = 0
            while (i < tmpl.length) {
                val ch = tmpl[i]
                if (ch == '\\' && i + 1 < tmpl.length) {
                    val nx = tmpl[i + 1]
                    if (nx in '0'..'9') {
                        if (sb.isNotEmpty()) { parts.add(sb.toString()); sb.setLength(0) }
                        parts.add(nx - '0')
                        i += 2
                        continue
                    }
                    when (nx) {
                        'n' -> { sb.append('\n'); i += 2; continue }
                        't' -> { sb.append('\t'); i += 2; continue }
                        '\\' -> { sb.append('\\'); i += 2; continue }
                        else -> { }
                    }
                }
                sb.append(ch)
                i++
            }
            if (sb.isNotEmpty()) parts.add(sb.toString())
        }
    }
    fun expand(m: Matcher, sb: StringBuilder) {
        for (p in parts) {
            if (p is String) sb.append(p)
            else if (p is Int) {
                if (p <= m.groupCount()) { val g = m.group(p); if (g != null) sb.append(g) }
            }
        }
    }
    /** returns replaced line or null if no match; count[0] += matches */
    fun applyLine(m: Matcher, t: String, count: IntArray): String? {
        m.reset(t)
        var last = 0
        var sb: StringBuilder? = null
        while (m.find()) {
            if (m.end() == m.start()) continue
            if (sb == null) sb = StringBuilder()
            sb.append(t, last, m.start())
            expand(m, sb)
            last = m.end()
            count[0] = count[0] + 1
        }
        if (sb == null) return null
        sb.append(t, last, t.length)
        return sb.toString()
    }
}

// ═══════════════════════════ custom editor view ═══════════════════════════
class EditorView(ctx: Context, val pane: Pane, val app: MainActivity) : View(ctx) {
    private val doc: Doc get() = pane.doc
    private val tp = Paint(Paint.ANTI_ALIAS_FLAG)
    private val numP = Paint(Paint.ANTI_ALIAS_FLAG)
    private val fillP = Paint()

    var fontFamily: String = "monospace"
    var fontSize: Int = 11
    var bold: Boolean = false
    var italic: Boolean = false
    var fg: Int = 0xFFD4D4D4.toInt()
    var bgc: Int = 0xFF1E1E1E.toInt()
    var wrap: Boolean = false
    var showNums: Boolean = true

    var caretL = 0
    var caretC = 0
    var ancL = 0
    var ancC = 0
    var topLine = 0
    var topPx = 0f
    var hx = 0f
    private var lineH = 20f
    private var charW = 10f
    private var ascent = 16f
    private var maxW = 0f
    private var caretOn = true
    private var composeLen = 0
    private var vDrag = false
    private var hDrag = false
    private var selecting = false
    private var mouseSel = false
    private var lastX = 0f
    private var lastY = 0f
    private var lockAxis = 0
    private var pinchSize = 11f
    private var lastFlingY = 0

    // overlays (0-based lines)
    var copyHl: IntArray? = null
    var rrHl: IntArray? = null
    var scmHl: IntArray? = null
    var scmStartLine = -1
    var delPreview: ArrayList<IntArray>? = null
    var foundL = -1
    var foundC1 = 0
    var foundC2 = 0
    val marks = HashMap<Int, ArrayList<IntArray>>()

    private val scroller = OverScroller(ctx)

    init {
        isFocusable = true
        isFocusableInTouchMode = true
        numP.textAlign = Paint.Align.RIGHT
        applyFont()
    }

    // ── fonts / metrics ──
    fun applyFont() {
        val style = (if (bold) Typeface.BOLD else 0) or (if (italic) Typeface.ITALIC else 0)
        tp.typeface = Typeface.create(fontFamily, style)
        numP.typeface = Typeface.create("monospace", Typeface.NORMAL)
        tp.textSize = fontSize * gDensity
        numP.textSize = tp.textSize
        val fm = tp.fontMetrics
        lineH = Math.ceil((fm.descent - fm.ascent + fm.leading).toDouble()).toFloat() + 2f
        ascent = -fm.ascent + 1f
        charW = tp.measureText("0")
        maxW = 0f
        invalidate()
    }

    private fun mono(): Boolean = fontFamily == "monospace"
    private fun bmW(): Float = dpf(14f)
    private fun barW(): Float = dpf(18f)
    private fun numW(): Float {
        if (!showNums) return 0f
        val digits = maxOf(3, doc.total.toString().length)
        return digits * numP.measureText("0") + dpf(10f)
    }
    private fun textLeft(): Float = bmW() + numW() + dpf(4f)
    private fun textW(): Float = maxOf(10f, width - textLeft() - barW())
    private fun textH(): Float = height - (if (wrap) 0f else barW())
    fun visRows(): Int = maxOf(1, (textH() / lineH).toInt())

    private fun disp(t: String): String = if (t.indexOf('\t') < 0) t else t.replace("\t", "    ")
    private fun dcol(t: String, col: Int): Int {
        if (t.indexOf('\t') < 0) return col
        var extra = 0
        val n = minOf(col, t.length)
        for (i in 0 until n) if (t[i] == '\t') extra += 3
        return col + extra
    }
    private fun rcol(t: String, d: Int): Int {
        if (t.indexOf('\t') < 0) return minOf(d, t.length)
        var acc = 0
        for (i in 0 until t.length) {
            val w = if (t[i] == '\t') 4 else 1
            if (d <= acc) return i
            if (d < acc + w) return if (d - acc >= 2) i + 1 else i
            acc += w
        }
        return t.length
    }

    private fun rowStarts(ds: String): IntArray {
        if (!wrap || ds.isEmpty()) return intArrayOf(0)
        val w = textW() - 2f
        if (w < charW * 2) return intArrayOf(0)
        val list = ArrayList<Int>()
        var s = 0
        val n = ds.length
        while (s < n) {
            list.add(s)
            val c = tp.breakText(ds, s, n, true, w, null)
            s += if (c <= 0) 1 else c
        }
        if (list.isEmpty()) list.add(0)
        return list.toIntArray()
    }

    private fun rowsOfLine(l: Int): Int = rowStarts(disp(doc.getLine(l))).size

    private fun xAt(ds: String, rs: Int, i: Int, x0: Float): Float {
        val n = i - rs
        if (n <= 0) return x0
        return x0 + (if (mono()) n * charW else tp.measureText(ds, rs, i))
    }

    // ── scrolling ──
    private fun maxTopLines(): Int {
        val tot = doc.total
        return if (wrap) maxOf(0, tot - 1) else maxOf(0, tot - visRows())
    }

    fun scrollByPx(dy: Double) {
        val tot = doc.total
        if (!wrap || Math.abs(dy) > lineH * 300.0) {
            var pos = topLine.toDouble() * lineH + topPx + dy
            val maxPos = maxTopLines().toDouble() * lineH
            if (pos < 0.0) pos = 0.0
            if (pos > maxPos) pos = maxPos
            var l = Math.floor(pos / lineH).toInt()
            if (l < 0) l = 0
            topLine = l
            topPx = (pos - l.toDouble() * lineH).toFloat()
        } else {
            var p = topPx + dy.toFloat()
            var l = topLine
            while (p < 0f) {
                if (l == 0) { p = 0f; break }
                l--
                p += rowsOfLine(l) * lineH
            }
            while (true) {
                val hh = rowsOfLine(l) * lineH
                if (p >= hh) {
                    if (l >= tot - 1) { p = maxOf(0f, hh - lineH); break }
                    p -= hh
                    l++
                } else break
            }
            topLine = l
            topPx = p
        }
        invalidate()
        app.onViewChanged(pane)
    }

    fun scrollLines(n: Int) { scrollByPx(n.toDouble() * lineH) }

    fun scrollToLine(ln: Int, center: Boolean) {
        val vis = visRows()
        if (!center && ln >= topLine && ln < topLine + vis - 1) return
        topLine = maxOf(0, minOf(ln - vis / 2, maxTopLines()))
        topPx = 0f
        invalidate()
        app.onViewChanged(pane)
    }

    fun ensureCaretVisible() {
        val tot = doc.total
        if (caretL >= tot) caretL = tot - 1
        if (caretL < 0) caretL = 0
        val t = doc.getLine(caretL)
        val ds = disp(t)
        val rows = rowStarts(ds)
        val dc = dcol(t, caretC)
        var r = 0
        for (i in rows.indices) if (rows[i] <= dc) r = i
        val th = textH()
        if (caretL < topLine || caretL - topLine > visRows() + 400) {
            topLine = maxOf(0, caretL - visRows() / 2)
            topPx = 0f
        } else {
            var y = -topPx
            var l = topLine
            while (l < caretL) { y += rowsOfLine(l) * lineH; l++ }
            val yTop = y + r * lineH
            val yBot = yTop + lineH
            if (yTop < 0f) scrollByPx(yTop.toDouble())
            else if (yBot > th) scrollByPx((yBot - th).toDouble())
        }
        if (!wrap) {
            val x = xAt(ds, 0, dc, 0f)
            val tw = textW()
            if (x - hx < 0f) hx = maxOf(0f, x - tw / 4f)
            else if (x - hx > tw - charW * 2f) hx = x - tw + tw / 4f
        } else hx = 0f
        invalidate()
    }

    // ── hit testing ──
    fun hit(px: Float, py0: Float): IntArray {
        val tot = doc.total
        val th = textH()
        val py = if (py0 < 0f) 0f else if (py0 > th - 1f) th - 1f else py0
        var y = -topPx
        var l = topLine
        var lastT = ""
        while (l < tot) {
            val t = doc.getLine(l)
            val ds = disp(t)
            val rows = rowStarts(ds)
            val h = rows.size * lineH
            if (py < y + h) {
                var row = ((py - y) / lineH).toInt()
                if (row < 0) row = 0
                if (row >= rows.size) row = rows.size - 1
                val rs = rows[row]
                val re = if (row + 1 < rows.size) rows[row + 1] else ds.length
                val relX = px - textLeft() + hx
                var di = rs
                if (relX > 0f) {
                    if (mono()) {
                        di = rs + Math.round(relX / charW)
                    } else {
                        val c = tp.breakText(ds, rs, re, true, relX, null)
                        di = rs + c
                        if (di < re) {
                            val wc = tp.measureText(ds, di, di + 1)
                            val pre = tp.measureText(ds, rs, di)
                            if (relX - pre > wc / 2f) di++
                        }
                    }
                }
                if (di > re) di = re
                if (di < rs) di = rs
                return intArrayOf(l, rcol(t, di))
            }
            y += h
            l++
            lastT = t
        }
        return intArrayOf(tot - 1, lastT.length)
    }

    // ── caret / selection ──
    val hasSel: Boolean get() = ancL != caretL || ancC != caretC

    fun selNorm(): IntArray =
        if (ancL < caretL || (ancL == caretL && ancC <= caretC)) intArrayOf(ancL, ancC, caretL, caretC)
        else intArrayOf(caretL, caretC, ancL, ancC)

    fun setCaret(l: Int, c: Int, extend: Boolean) {
        val tot = doc.total
        val ll = l.coerceIn(0, tot - 1)
        val t = doc.getLine(ll)
        val cc = c.coerceIn(0, t.length)
        caretL = ll
        caretC = cc
        if (!extend) { ancL = ll; ancC = cc }
        caretOn = true
        invalidate()
        app.onViewChanged(pane)
    }

    fun clearOverlays() {
        marks.clear(); foundL = -1
        copyHl = null; rrHl = null; scmHl = null; scmStartLine = -1; delPreview = null
    }

    // ── drawing ──
    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val d = doc
        val tot = d.total
        val th = textH()
        val tl = textLeft()
        val tw = textW()
        canvas.drawColor(bgc)
        fillP.color = 0xFF1A1A1A.toInt()
        canvas.drawRect(0f, 0f, bmW(), th, fillP)
        fillP.color = 0xFF252525.toInt()
        canvas.drawRect(bmW(), 0f, tl - dpf(4f), th, fillP)
        val sn: IntArray? = if (hasSel) selNorm() else null
        var ln = minOf(topLine, maxOf(0, tot - 1))
        var y = -topPx
        while (y < th && ln < tot) {
            val t = d.getLine(ln)
            val ds = disp(t)
            val rows = rowStarts(ds)
            drawOneLine(canvas, ln, t, ds, rows, y, tl, tw, th, sn)
            y += rows.size * lineH
            ln++
        }
        drawBars(canvas, th, tw)
    }

    private fun inRange(r: IntArray?, ln: Int): Boolean = r != null && ln >= r[0] && ln <= r[1]

    private fun fillSpan(canvas: Canvas, ds: String, rs: Int, re: Int, ry: Float, x0: Float, a: Int, b: Int,
                         color: Int, lastRow: Boolean, nl: Boolean) {
        val aa = maxOf(a, rs)
        val bb = minOf(b, re)
        val extra = nl && lastRow && b > re && a <= re
        if (bb <= aa && !extra) return
        val x1 = xAt(ds, rs, aa, x0)
        var x2 = xAt(ds, rs, maxOf(bb, aa), x0)
        if (extra) x2 += charW * 0.6f
        fillP.color = color
        canvas.drawRect(x1, ry, x2, ry + lineH, fillP)
    }

    private fun drawOneLine(canvas: Canvas, ln: Int, t: String, ds: String, rows: IntArray, y: Float,
                            tl: Float, tw: Float, th: Float, sn: IntArray?) {
        val rh = rows.size * lineH
        var lbg = 0
        var lfg = 0
        if (ln == caretL && sn == null) lbg = 0xFF2A2A2A.toInt()
        if (pane.bmLines.contains(ln)) { lbg = 0xFF1A3A1A.toInt(); lfg = 0xFFC8FFC8.toInt() }
        if (inRange(copyHl, ln)) { lbg = 0xFF264F78.toInt(); lfg = 0xFFD4D4D4.toInt() }
        if (inRange(rrHl, ln)) { lbg = 0xFF4A3A00.toInt(); lfg = 0xFFF0D060.toInt() }
        if (inRange(scmHl, ln)) { lbg = 0xFF264F78.toInt(); lfg = 0xFFD4D4D4.toInt() }
        if (ln == scmStartLine) { lbg = 0xFF4A3A00.toInt(); lfg = 0xFFF0D060.toInt() }
        val dpv = delPreview
        if (dpv != null) {
            for (r in dpv) if (ln >= r[0] && ln <= r[1]) { lbg = 0xFFFADBD8.toInt(); lfg = 0xFFC0392B.toInt() }
        }
        if (lbg != 0) {
            fillP.color = lbg
            canvas.drawRect(tl, y, tl + tw, y + rh, fillP)
        }
        val textColor = if (lfg != 0) lfg else fg

        // gutter: number + bookmark dot
        if (y + rh > 0f) {
            if (showNums) {
                numP.color = if (ln == caretL) 0xFFD4D4D4.toInt() else 0xFF858585.toInt()
                canvas.drawText((ln + 1).toString(), tl - dpf(8f), y + ascent, numP)
            }
            if (pane.bmLines.contains(ln)) {
                val cxm = bmW() / 2f
                val cym = y + lineH / 2f
                fillP.style = Paint.Style.FILL
                fillP.color = 0xFF2D7DD2.toInt()
                canvas.drawCircle(cxm, cym, dpf(5f), fillP)
                fillP.style = Paint.Style.STROKE
                fillP.strokeWidth = dpf(1.5f)
                fillP.color = 0xFFBFE0FF.toInt()
                canvas.drawCircle(cxm, cym, dpf(5f), fillP)
                fillP.style = Paint.Style.FILL
            }
        }

        var sa = -1
        var sb = -1
        if (sn != null && ln >= sn[0] && ln <= sn[2]) {
            val c1 = if (ln == sn[0]) sn[1] else 0
            sa = dcol(t, c1)
            sb = if (ln == sn[2]) dcol(t, sn[3]) else ds.length + 1
        }
        val mk = marks[ln]
        val x0 = tl - (if (wrap) 0f else hx)

        canvas.save()
        canvas.clipRect(tl, 0f, tl + tw, th)
        for (r in rows.indices) {
            val ry = y + r * lineH
            if (ry + lineH < 0f || ry > th) continue
            val rs = rows[r]
            val re = if (r + 1 < rows.size) rows[r + 1] else ds.length
            val lastRow = r == rows.size - 1
            if (!wrap) {
                val w = xAt(ds, rs, re, 0f)
                if (w > maxW) maxW = w
            }
            if (mk != null) for (m in mk) fillSpan(canvas, ds, rs, re, ry, x0, dcol(t, m[0]), dcol(t, m[1]), MARK_COLOURS[m[2]], lastRow, false)
            if (ln == foundL) fillSpan(canvas, ds, rs, re, ry, x0, dcol(t, foundC1), dcol(t, foundC2), 0xFFFF8C00.toInt(), lastRow, false)
            if (sa >= 0) fillSpan(canvas, ds, rs, re, ry, x0, sa, sb, 0xFF264F78.toInt(), lastRow, true)
            // text (clip very long rows to what is visible)
            var from = rs
            var to = re
            if (!wrap && re - rs > 3000) {
                val per = maxOf(charW, 1f)
                from = maxOf(rs, rs + (hx / per).toInt() - 6)
                to = minOf(re, from + (tw / per).toInt() + 16)
            }
            if (to > from) {
                tp.color = textColor
                canvas.drawText(ds, from, to, xAt(ds, rs, from, x0), ry + ascent, tp)
                if (ln == foundL || mk != null) {
                    if (ln == foundL) overText(canvas, ds, rs, re, from, to, ry, x0, dcol(t, foundC1), dcol(t, foundC2))
                    if (mk != null) for (m in mk) overText(canvas, ds, rs, re, from, to, ry, x0, dcol(t, m[0]), dcol(t, m[1]))
                }
            }
            if (ln == caretL && caretOn && !hasSel) {
                val dc = dcol(t, caretC)
                val inRow = dc >= rs && (dc < re || (lastRow && dc <= re))
                if (inRow) {
                    val cx = xAt(ds, rs, dc, x0)
                    fillP.color = 0xFFFFFFFF.toInt()
                    canvas.drawRect(cx, ry + 1f, cx + dpf(2f), ry + lineH - 1f, fillP)
                }
            }
        }
        canvas.restore()
    }

    private fun overText(canvas: Canvas, ds: String, rs: Int, re: Int, from: Int, to: Int, ry: Float, x0: Float, a: Int, b: Int) {
        val aa = maxOf(a, from)
        val bb = minOf(b, to)
        if (bb <= aa) return
        val x1 = xAt(ds, rs, aa, x0)
        val x2 = xAt(ds, rs, bb, x0)
        canvas.save()
        canvas.clipRect(x1, ry, x2, ry + lineH)
        tp.color = 0xFF000000.toInt()
        canvas.drawText(ds, from, to, xAt(ds, rs, from, x0), ry + ascent, tp)
        canvas.restore()
    }

    private fun thumbH(th: Float): Float {
        val tot = maxOf(1, doc.total)
        val h = th * visRows().toFloat() / tot.toFloat()
        return minOf(th, maxOf(dpf(36f), h))
    }

    private fun drawBars(canvas: Canvas, th: Float, tw: Float) {
        val bw = barW()
        fillP.color = 0xFF252525.toInt()
        canvas.drawRect(width - bw, 0f, width.toFloat(), th, fillP)
        val tot = doc.total
        val maxTop = maxOf(1, maxTopLines()).toDouble()
        val pos = topLine.toDouble() + topPx.toDouble() / lineH.toDouble()
        val frac = Math.min(1.0, Math.max(0.0, pos / maxTop))
        val tH = thumbH(th)
        val ty = (frac * (th - tH).toDouble()).toFloat()
        fillP.color = if (vDrag) 0xFFA0A0A0.toInt() else 0xFF606060.toInt()
        canvas.drawRect(width - bw + dpf(4f), ty, width - dpf(4f), ty + tH, fillP)
        if (!wrap) {
            fillP.color = 0xFF252525.toInt()
            canvas.drawRect(0f, th, width.toFloat(), height.toFloat(), fillP)
            val cw = maxOf(maxW + charW * 2f, tw)
            val thw = maxOf(dpf(36f), tw * tw / cw)
            val hf = if (cw - tw <= 1f) 0f else Math.min(1f, Math.max(0f, hx / (cw - tw)))
            val tx = textLeft() + hf * (tw - thw)
            fillP.color = if (hDrag) 0xFFA0A0A0.toInt() else 0xFF606060.toInt()
            canvas.drawRect(tx, th + dpf(4f), tx + thw, height - dpf(4f), fillP)
        }
    }

    private fun dragV(y: Float) {
        val th = textH()
        val tH = thumbH(th)
        val frac = Math.min(1.0, Math.max(0.0, ((y - tH / 2f) / maxOf(1f, th - tH)).toDouble()))
        topLine = (frac * maxTopLines().toDouble()).toInt()
        topPx = 0f
        invalidate()
        app.onViewChanged(pane)
    }

    private fun dragH(x: Float) {
        val tw = textW()
        val cw = maxOf(maxW + charW * 2f, tw)
        val thw = maxOf(dpf(36f), tw * tw / cw)
        val f = Math.min(1f, Math.max(0f, (x - textLeft() - thw / 2f) / maxOf(1f, tw - thw)))
        hx = f * maxOf(0f, cw - tw)
        invalidate()
    }

    // ── touch / mouse ──
    private val gd = GestureDetector(ctx, object : GestureDetector.SimpleOnGestureListener() {
        override fun onDown(e: MotionEvent): Boolean {
            scroller.forceFinished(true)
            lockAxis = 0
            return true
        }
        override fun onSingleTapUp(e: MotionEvent): Boolean {
            handleTap(e.x, e.y, false)
            return true
        }
        override fun onScroll(e1: MotionEvent?, e2: MotionEvent, distanceX: Float, distanceY: Float): Boolean {
            if (lockAxis == 0) lockAxis = if (!wrap && Math.abs(distanceX) > Math.abs(distanceY) * 1.5f) 1 else 2
            if (lockAxis == 1) {
                hx = maxOf(0f, hx + distanceX)
                invalidate()
            } else scrollByPx(distanceY.toDouble())
            return true
        }
        override fun onFling(e1: MotionEvent?, e2: MotionEvent, velocityX: Float, velocityY: Float): Boolean {
            if (lockAxis == 1) return true
            lastFlingY = 0
            scroller.fling(0, 0, 0, velocityY.toInt(), 0, 0, -1000000000, 1000000000)
            postOnAnimation(flingRun)
            return true
        }
        override fun onLongPress(e: MotionEvent) {
            if (e.x < textLeft() - dpf(2f)) return
            val h = hit(e.x, e.y)
            selectWordAt(h[0], h[1])
            selecting = true
            startEdge()
        }
        override fun onDoubleTap(e: MotionEvent): Boolean {
            if (e.x >= textLeft() && e.x < width - barW()) {
                val h = hit(e.x, e.y)
                selectWordAt(h[0], h[1])
            }
            return true
        }
    })

    private val scale = ScaleGestureDetector(ctx, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
        override fun onScaleBegin(detector: ScaleGestureDetector): Boolean {
            pinchSize = fontSize.toFloat()
            return true
        }
        override fun onScale(detector: ScaleGestureDetector): Boolean {
            pinchSize = Math.min(72f, Math.max(6f, pinchSize * detector.scaleFactor))
            val ns = Math.round(pinchSize)
            if (ns != fontSize) { fontSize = ns; applyFont() }
            return true
        }
    })

    private val flingRun = object : Runnable {
        override fun run() {
            if (scroller.computeScrollOffset()) {
                val cy = scroller.currY
                val dy = cy - lastFlingY
                lastFlingY = cy
                val f = Math.max(1.0, Math.min(doc.total / 50000.0, 300.0))
                scrollByPx(-dy.toDouble() * f)
                postOnAnimation(this)
            }
        }
    }

    private val edgeRun = object : Runnable {
        override fun run() {
            if (!(selecting || mouseSel)) return
            val th = textH()
            if (lastY < dpf(24f)) scrollByPx(-lineH * 0.7)
            else if (lastY > th - dpf(24f)) scrollByPx(lineH * 0.7)
            val h = hit(lastX, lastY)
            setCaret(h[0], h[1], true)
            postDelayed(this, 40)
        }
    }

    private fun startEdge() {
        removeCallbacks(edgeRun)
        postDelayed(edgeRun, 60)
    }

    private fun isWordCh(c: Char): Boolean = Character.isLetterOrDigit(c) || c == '_'

    fun selectWordAt(l: Int, c: Int) {
        val t = doc.getLine(l)
        var a = minOf(c, t.length)
        var b = a
        while (a > 0 && isWordCh(t[a - 1])) a--
        while (b < t.length && isWordCh(t[b])) b++
        ancL = l; ancC = a; caretL = l; caretC = b
        caretOn = true
        invalidate()
        app.onViewChanged(pane)
    }

    fun handleTap(x: Float, y: Float, secondary: Boolean) {
        requestFocus()
        val h = hit(maxOf(x, textLeft()), y)
        val line = h[0]
        if (x < textLeft() - dpf(2f)) {
            // gutter: Notepad++-style bookmark toggle (Special Copy / Delete-Lines pick modes use it to select lines)
            val consumed = app.onNumberTap(pane, line)
            if (!consumed) app.toggleBookmarkAt(pane, line)
            return
        }
        setCaret(h[0], h[1], false)
        val noKb = app.onTextTap(pane, line)
        if (!noKb) showKeyboard()
    }

    fun showKeyboard() {
        val imm = context.getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        imm.showSoftInput(this, 0)
    }

    override fun onTouchEvent(ev: MotionEvent): Boolean {
        val act = ev.actionMasked
        lastX = ev.x
        lastY = ev.y
        if (act == MotionEvent.ACTION_DOWN) {
            vDrag = false; hDrag = false; selecting = false; mouseSel = false
            if (ev.x > width - dpf(26f)) { vDrag = true; dragV(ev.y); return true }
            if (!wrap && ev.y > textH()) { hDrag = true; dragH(ev.x); return true }
        }
        if (vDrag) {
            if (act == MotionEvent.ACTION_MOVE) dragV(ev.y)
            if (act == MotionEvent.ACTION_UP || act == MotionEvent.ACTION_CANCEL) { vDrag = false; invalidate() }
            return true
        }
        if (hDrag) {
            if (act == MotionEvent.ACTION_MOVE) dragH(ev.x)
            if (act == MotionEvent.ACTION_UP || act == MotionEvent.ACTION_CANCEL) { hDrag = false; invalidate() }
            return true
        }
        if (ev.getToolType(0) == MotionEvent.TOOL_TYPE_MOUSE) return mouseTouch(ev)
        if (selecting) {
            if (act == MotionEvent.ACTION_MOVE) {
                val h = hit(ev.x, ev.y)
                setCaret(h[0], h[1], true)
            } else if (act == MotionEvent.ACTION_UP || act == MotionEvent.ACTION_CANCEL) {
                selecting = false
                removeCallbacks(edgeRun)
            }
            return true
        }
        scale.onTouchEvent(ev)
        if (!scale.isInProgress) gd.onTouchEvent(ev)
        return true
    }

    private fun mouseTouch(ev: MotionEvent): Boolean {
        when (ev.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                requestFocus()
                if (ev.x < textLeft()) {
                    handleTap(ev.x, ev.y, (ev.buttonState and MotionEvent.BUTTON_SECONDARY) != 0)
                } else {
                    val h = hit(ev.x, ev.y)
                    setCaret(h[0], h[1], false)
                    val noKb = app.onTextTap(pane, h[0])
                    if (!noKb) showKeyboard()
                    mouseSel = true
                    startEdge()
                }
            }
            MotionEvent.ACTION_MOVE -> {
                if (mouseSel) {
                    val h = hit(ev.x, ev.y)
                    setCaret(h[0], h[1], true)
                }
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                mouseSel = false
                removeCallbacks(edgeRun)
            }
        }
        return true
    }

    override fun onGenericMotionEvent(ev: MotionEvent): Boolean {
        if (ev.actionMasked == MotionEvent.ACTION_SCROLL) {
            val v = ev.getAxisValue(MotionEvent.AXIS_VSCROLL)
            val h = ev.getAxisValue(MotionEvent.AXIS_HSCROLL)
            if ((ev.metaState and KeyEvent.META_CTRL_ON) != 0) {
                if (v > 0f) app.zoomBy(1) else if (v < 0f) app.zoomBy(-1)
            } else if ((ev.metaState and KeyEvent.META_SHIFT_ON) != 0) {
                hx = maxOf(0f, hx - v * dpf(40f))
                invalidate()
            } else {
                if (v != 0f) scrollByPx((-v * lineH * 3f).toDouble())
                if (h != 0f && !wrap) { hx = maxOf(0f, hx + h * dpf(40f)); invalidate() }
            }
            return true
        }
        return super.onGenericMotionEvent(ev)
    }

    // ── blink ──
    private val blink = object : Runnable {
        override fun run() {
            caretOn = !caretOn
            invalidate()
            postDelayed(this, 530)
        }
    }
    override fun onAttachedToWindow() { super.onAttachedToWindow(); postDelayed(blink, 530) }
    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        removeCallbacks(blink); removeCallbacks(edgeRun); removeCallbacks(flingRun)
    }
    override fun onSizeChanged(w: Int, h: Int, ow: Int, oh: Int) { super.onSizeChanged(w, h, ow, oh); invalidate() }

    // ═════════ editing ═════════
    private fun editable(): Boolean {
        if (doc.indexing) { app.toast("Still indexing the file — editing unlocks when indexing finishes"); return false }
        return true
    }

    fun clampCaret() {
        val l = caretL.coerceIn(0, doc.total - 1)
        caretL = l
        caretC = caretC.coerceIn(0, doc.getLine(l).length)
        ancL = caretL
        ancC = caretC
    }

    fun afterEdit() {
        pane.clearDocRedo()
        clearOverlays()
        pane.onTextChanged()
        app.onEdited(pane)
        caretOn = true
        ensureCaretVisible()
        invalidate()
    }

    fun insertText(s0: String, key: String?) {
        if (!editable()) return
        val s = s0.replace("\r\n", "\n").replace('\r', '\n')
        var sl = caretL
        var sc = caretC
        var el = caretL
        var ec = caretC
        if (hasSel) { val a = selNorm(); sl = a[0]; sc = a[1]; el = a[2]; ec = a[3] }
        val first = doc.getLine(sl)
        val last = if (el == sl) first else doc.getLine(el)
        val prefix = first.substring(0, minOf(sc, first.length))
        val suffix = last.substring(minOf(ec, last.length))
        val joined = prefix + s + suffix
        val nlIdx = s.lastIndexOf('\n')
        val parts: Array<String> = if (nlIdx < 0) arrayOf(joined) else joined.split("\n").toTypedArray()
        var nlCount = 0
        for (ch in s) if (ch == '\n') nlCount++
        val nl = sl + nlCount
        val nc = if (nlIdx < 0) sc + s.length else s.length - (nlIdx + 1)
        doc.edit(sl, el + 1, parts, caretL, caretC, key)
        caretL = nl; caretC = nc; ancL = nl; ancC = nc
        afterEdit()
    }

    fun deleteSel() {
        if (!hasSel || !editable()) return
        val a = selNorm()
        val first = doc.getLine(a[0])
        val last = if (a[2] == a[0]) first else doc.getLine(a[2])
        val joined = first.substring(0, minOf(a[1], first.length)) + last.substring(minOf(a[3], last.length))
        doc.edit(a[0], a[2] + 1, arrayOf(joined), caretL, caretC, null)
        caretL = a[0]; caretC = a[1]; ancL = caretL; ancC = caretC
        afterEdit()
    }

    fun backspace() {
        if (!editable()) return
        if (hasSel) { deleteSel(); return }
        if (caretC > 0) {
            val t = doc.getLine(caretL)
            var n = 1
            if (caretC >= 2 && caretC <= t.length && Character.isLowSurrogate(t[caretC - 1]) && Character.isHighSurrogate(t[caretC - 2])) n = 2
            val nt = t.substring(0, caretC - n) + t.substring(minOf(caretC, t.length))
            doc.edit(caretL, caretL + 1, arrayOf(nt), caretL, caretC, "b$caretL")
            caretC -= n; ancC = caretC
            afterEdit()
        } else if (caretL > 0) {
            val prev = doc.getLine(caretL - 1)
            val cur = doc.getLine(caretL)
            doc.edit(caretL - 1, caretL + 1, arrayOf(prev + cur), caretL, caretC, null)
            caretL -= 1; caretC = prev.length; ancL = caretL; ancC = caretC
            afterEdit()
        }
    }

    fun deleteFwd() {
        if (!editable()) return
        if (hasSel) { deleteSel(); return }
        val t = doc.getLine(caretL)
        if (caretC < t.length) {
            val nt = t.substring(0, caretC) + t.substring(caretC + 1)
            doc.edit(caretL, caretL + 1, arrayOf(nt), caretL, caretC, "d$caretL")
            afterEdit()
        } else if (caretL < doc.total - 1) {
            val nx = doc.getLine(caretL + 1)
            doc.edit(caretL, caretL + 2, arrayOf(t + nx), caretL, caretC, null)
            afterEdit()
        }
    }

    fun typeString(s: String, composing: Boolean) {
        if (!composing && s.length == 1 && app.preChar(pane, s[0])) return
        val key: String? = if (s.indexOf('\n') < 0 && s.length <= 2) "t$caretL" else null
        insertText(s, key)
    }

    fun doUndo() {
        val sn = doc.undoOp(caretL, caretC)
        if (sn != null) { restoreFrom(sn); return }
        if (pane.docUndo.isNotEmpty()) { app.swapDoc(pane, true); return }
        app.toast("Nothing to undo")
    }

    fun doRedo() {
        val sn = doc.redoOp(caretL, caretC)
        if (sn != null) { restoreFrom(sn); return }
        if (pane.docRedo.isNotEmpty()) { app.swapDoc(pane, false); return }
        app.toast("Nothing to redo")
    }

    private fun restoreFrom(sn: Snap) {
        clearOverlays()
        val l = sn.cl.coerceIn(0, doc.total - 1)
        caretL = l
        caretC = sn.cc.coerceIn(0, doc.getLine(l).length)
        ancL = caretL; ancC = caretC
        pane.onTextChanged()
        app.onEdited(pane)
        ensureCaretVisible()
        invalidate()
    }

    // ── clipboard ──
    private fun clipSet(s: String) {
        val cm = context.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        cm.setPrimaryClip(ClipData.newPlainText("text", s))
    }

    fun copySel(cut: Boolean) {
        if (hasSel) {
            val a = selNorm()
            val text = doc.getText(a[0], a[1], a[2], a[3], 900000)
            if (text == null) { app.toast("Selection too large for the clipboard — use Special Copy Mode to save it to a file"); return }
            clipSet(text)
            if (cut) deleteSel()
            app.toast("✔ Copied")
        } else {
            val t = doc.getLine(caretL)
            clipSet(t)
            if (cut) {
                if (!editable()) return
                if (caretL < doc.total - 1) doc.deleteRanges(listOf(intArrayOf(caretL, caretL)), caretL, caretC)
                else doc.edit(caretL, caretL + 1, arrayOf(""), caretL, caretC, null)
                caretC = 0; ancC = 0
                afterEdit()
                app.toast("✂ Line cut")
            } else app.toast("✔ Line ${caretL + 1} copied")
        }
    }

    fun paste() {
        val cm = context.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        val clip = cm.primaryClip
        if (clip != null && clip.itemCount > 0) {
            val s = clip.getItemAt(0).coerceToText(context).toString()
            if (s.isNotEmpty()) insertText(s, null)
        }
    }

    fun selectAll() {
        ancL = 0; ancC = 0
        caretL = doc.total - 1
        caretC = doc.getLine(caretL).length
        invalidate()
        app.onViewChanged(pane)
    }

    // ── keyboard ──
    private fun lineLen(l: Int): Int = doc.getLine(l).length

    override fun onKeyDown(keyCode: Int, ev: KeyEvent): Boolean {
        val shift = ev.isShiftPressed
        val ctrl = ev.isCtrlPressed
        val tot = doc.total
        if (ctrl && !ev.isAltPressed) {
            when (keyCode) {
                KeyEvent.KEYCODE_MOVE_HOME -> { setCaret(0, 0, shift); ensureCaretVisible(); return true }
                KeyEvent.KEYCODE_MOVE_END -> { setCaret(tot - 1, lineLen(tot - 1), shift); ensureCaretVisible(); return true }
            }
            return false
        }
        when (keyCode) {
            KeyEvent.KEYCODE_DPAD_LEFT -> {
                if (caretC > 0) setCaret(caretL, caretC - 1, shift)
                else if (caretL > 0) setCaret(caretL - 1, lineLen(caretL - 1), shift)
                ensureCaretVisible(); return true
            }
            KeyEvent.KEYCODE_DPAD_RIGHT -> {
                if (caretC < lineLen(caretL)) setCaret(caretL, caretC + 1, shift)
                else if (caretL < tot - 1) setCaret(caretL + 1, 0, shift)
                ensureCaretVisible(); return true
            }
            KeyEvent.KEYCODE_DPAD_UP -> { if (caretL > 0) setCaret(caretL - 1, caretC, shift); ensureCaretVisible(); return true }
            KeyEvent.KEYCODE_DPAD_DOWN -> { if (caretL < tot - 1) setCaret(caretL + 1, caretC, shift); ensureCaretVisible(); return true }
            KeyEvent.KEYCODE_MOVE_HOME -> { setCaret(caretL, 0, shift); ensureCaretVisible(); return true }
            KeyEvent.KEYCODE_MOVE_END -> { setCaret(caretL, lineLen(caretL), shift); ensureCaretVisible(); return true }
            KeyEvent.KEYCODE_PAGE_UP -> { setCaret(maxOf(0, caretL - visRows()), caretC, shift); ensureCaretVisible(); return true }
            KeyEvent.KEYCODE_PAGE_DOWN -> { setCaret(minOf(tot - 1, caretL + visRows()), caretC, shift); ensureCaretVisible(); return true }
            KeyEvent.KEYCODE_DEL -> { backspace(); return true }
            KeyEvent.KEYCODE_FORWARD_DEL -> { deleteFwd(); return true }
            KeyEvent.KEYCODE_ENTER, KeyEvent.KEYCODE_NUMPAD_ENTER -> { insertText("\n", null); return true }
            KeyEvent.KEYCODE_TAB -> { insertText("\t", null); return true }
            KeyEvent.KEYCODE_ESCAPE -> { ancL = caretL; ancC = caretC; invalidate(); return true }
            KeyEvent.KEYCODE_SHIFT_LEFT, KeyEvent.KEYCODE_SHIFT_RIGHT, KeyEvent.KEYCODE_CTRL_LEFT,
            KeyEvent.KEYCODE_CTRL_RIGHT, KeyEvent.KEYCODE_ALT_LEFT, KeyEvent.KEYCODE_ALT_RIGHT,
            KeyEvent.KEYCODE_CAPS_LOCK, KeyEvent.KEYCODE_BACK, KeyEvent.KEYCODE_VOLUME_UP,
            KeyEvent.KEYCODE_VOLUME_DOWN -> return super.onKeyDown(keyCode, ev)
            else -> {
                if (ev.isAltPressed || ev.isMetaPressed) return super.onKeyDown(keyCode, ev)
                val u = ev.unicodeChar
                if (u > 0 && (u and KeyCharacterMap.COMBINING_ACCENT) == 0) {
                    typeString(String(Character.toChars(u)), false)
                    return true
                }
            }
        }
        return super.onKeyDown(keyCode, ev)
    }

    // ── soft keyboard connection ──
    override fun onCheckIsTextEditor(): Boolean = true

    override fun onCreateInputConnection(outAttrs: EditorInfo): InputConnection {
        outAttrs.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE or
            InputType.TYPE_TEXT_FLAG_NO_SUGGESTIONS or InputType.TYPE_TEXT_VARIATION_VISIBLE_PASSWORD
        outAttrs.imeOptions = EditorInfo.IME_FLAG_NO_FULLSCREEN or EditorInfo.IME_FLAG_NO_EXTRACT_UI
        composeLen = 0
        return EditConn(this)
    }

    private fun deleteBefore(n: Int) {
        var k = n
        while (k > 0) { backspace(); k-- }
    }

    inner class EditConn(v: View) : BaseInputConnection(v, false) {
        override fun commitText(text: CharSequence?, newCursorPosition: Int): Boolean {
            if (composeLen > 0) { deleteBefore(composeLen); composeLen = 0 }
            if (text != null && text.isNotEmpty()) typeString(text.toString(), false)
            return true
        }
        override fun setComposingText(text: CharSequence?, newCursorPosition: Int): Boolean {
            val s = if (text == null) "" else text.toString()
            if (composeLen > 0) { deleteBefore(composeLen); composeLen = 0 }
            if (s.isNotEmpty() && s.indexOf('\n') < 0) { typeString(s, true); composeLen = s.length }
            else if (s.isNotEmpty()) typeString(s, false)
            return true
        }
        override fun finishComposingText(): Boolean { composeLen = 0; return true }
        override fun deleteSurroundingText(beforeLength: Int, afterLength: Int): Boolean {
            composeLen = 0
            var b = beforeLength
            while (b > 0) { backspace(); b-- }
            var a = afterLength
            while (a > 0) { deleteFwd(); a-- }
            return true
        }
        override fun sendKeyEvent(event: KeyEvent): Boolean {
            if (event.action == KeyEvent.ACTION_DOWN) onKeyDown(event.keyCode, event)
            return true
        }
        override fun performEditorAction(actionCode: Int): Boolean { insertText("\n", null); return true }
        override fun getTextBeforeCursor(n: Int, flags: Int): CharSequence {
            val t = doc.getLine(caretL)
            val e = minOf(caretC, t.length)
            return t.substring(maxOf(0, e - n), e)
        }
        override fun getTextAfterCursor(n: Int, flags: Int): CharSequence {
            val t = doc.getLine(caretL)
            val s = minOf(caretC, t.length)
            return t.substring(s, minOf(t.length, s + n))
        }
        override fun beginBatchEdit(): Boolean = true
        override fun endBatchEdit(): Boolean = true
    }
}

// ═══════════════════════════ pane / tab ═══════════════════════════
class Bm(val line: Int, var name: String)

class MaxHeightScroll(ctx: Context) : ScrollView(ctx) {
    override fun onMeasure(w: Int, h: Int) {
        var mh = (resources.displayMetrics.heightPixels * 0.42f).toInt()
        val avail = MeasureSpec.getSize(h)
        if (avail > 0) mh = minOf(mh, (avail * 0.55f).toInt())
        super.onMeasure(w, MeasureSpec.makeMeasureSpec(mh, MeasureSpec.AT_MOST))
    }
}

class DelRow(val frame: LinearLayout, val startLbl: TextView, val endLbl: TextView,
             val startEt: EditText, val endEt: EditText, val pickBtn: Button) {
    var s: Int = -1
    var e: Int = -1
    var active: Boolean = true
}

class Parsed(val pairs: ArrayList<IntArray>, val bad: ArrayList<Int>)
class ReplaceResult(var count: Int, var newLines: Array<String>?, var workFile: File?)

class Pane(val app: MainActivity, val id: Int) {
    var doc: Doc = Doc()
    var fileName: String = ""
    val bookmarks = ArrayList<Bm>()
    val bmLines = HashSet<Int>()
    var speed: Double = 3.0
    var dir: String = "down"
    var scrollActive = false
    var acc = 0.0
    var wcVer = -1
    var wcWords = 0
    var wcChars = 0
    lateinit var view: EditorView

    private val scrollRun: Runnable = object : Runnable {
        override fun run() {
            if (!scrollActive) return
            acc += speed * 0.03
            if (acc >= 1.0) {
                val n = acc.toInt()
                acc -= n.toDouble()
                view.scrollLines(if (dir == "down") n else -n)
                app.onAutoScrollTick(this@Pane)
            }
            app.ui.postDelayed(this, 30)
        }
    }

    fun startScroll() {
        if (scrollActive) return
        scrollActive = true
        acc = 0.0
        app.ui.postDelayed(scrollRun, 30)
    }

    fun stopScroll() {
        scrollActive = false
        app.ui.removeCallbacks(scrollRun)
    }

    fun label(): String = (if (doc.modified) "*" else "") + (if (fileName.isEmpty()) "Untitled" else fileName)

    fun rebuildBm() {
        bmLines.clear()
        for (b in bookmarks) bmLines.add(b.line)
        view.invalidate()
    }

    fun onTextChanged() {
        app.refreshTabs()
        app.sessionDirty = true
    }

    fun replaceDoc(d: Doc) {
        val old = doc
        doc = d
        d.progress = Runnable { if (doc === d) app.onIndexProgress(this) }
        if (old !== d) {
            old.close()
            if (old.srcKind == "file" && old.srcRef != d.srcRef) {
                try { File(old.srcRef).delete() } catch (e: Exception) { }
            }
        }
    }

    // previous documents kept so a large Replace All can be undone / redone
    val docUndo = ArrayList<Doc>()
    val docRedo = ArrayList<Doc>()

    fun dropDoc(d: Doc) {
        d.close()
        if (d.srcKind == "file") {
            try { File(d.srcRef).delete() } catch (e: Exception) { }
        }
    }

    private fun wire(d: Doc) {
        d.progress = Runnable { if (doc === d) app.onIndexProgress(this) }
    }

    fun swapIn(nd: Doc) {
        clearDocRedo()
        docUndo.add(doc)
        while (docUndo.size > 3) dropDoc(docUndo.removeAt(0))
        doc = nd
        wire(nd)
    }

    fun undoSwap(): Boolean {
        if (docUndo.isEmpty()) return false
        docRedo.add(doc)
        doc = docUndo.removeAt(docUndo.size - 1)
        wire(doc)
        return true
    }

    fun redoSwap(): Boolean {
        if (docRedo.isEmpty()) return false
        docUndo.add(doc)
        doc = docRedo.removeAt(docRedo.size - 1)
        wire(doc)
        return true
    }

    fun clearDocRedo() {
        for (d in docRedo) dropDoc(d)
        docRedo.clear()
    }

    fun clearKept() {
        for (d in docUndo) dropDoc(d)
        for (d in docRedo) dropDoc(d)
        docUndo.clear()
        docRedo.clear()
    }

    fun dropKeptFor(ref: String) {
        val a = docUndo.filter { it.srcKind == "uri" && it.srcRef == ref }
        for (d in a) { docUndo.remove(d); dropDoc(d) }
        val b = docRedo.filter { it.srcKind == "uri" && it.srcRef == ref }
        for (d in b) { docRedo.remove(d); dropDoc(d) }
    }

    fun closePane() {
        stopScroll()
        clearKept()
        val d = doc
        d.close()
        if (d.srcKind == "file") {
            try { File(d.srcRef).delete() } catch (e: Exception) { }
        }
    }
}

// ═══════════════════════════ main activity ═══════════════════════════
class MainActivity : Activity() {
    val ui = Handler(Looper.getMainLooper())
    val panes = ArrayList<Pane>()
    var cur: Pane? = null
    private var counter = 0
    var sessionDirty = false

    private val RC_OPEN = 1
    private val RC_SAVEAS = 3
    private val RC_SCMFILE = 4

    private val cBg = 0xFF1E1E1E.toInt()
    private val cBar = 0xFF2D2D2D.toInt()
    private val cWhite = 0xFFFFFFFF.toInt()
    private val cTxt = 0xFFD4D4D4.toInt()

    private lateinit var root: LinearLayout
    private lateinit var toolbarBox: LinearLayout
    private lateinit var tabStrip: LinearLayout
    private lateinit var tabScroll: HorizontalScrollView
    private lateinit var editorHost: FrameLayout
    private lateinit var statusTv: TextView
    private lateinit var autosaveTv: TextView
    private lateinit var panelScroll: MaxHeightScroll
    private lateinit var findPanel: LinearLayout
    private lateinit var toolsPanel: LinearLayout
    private lateinit var delPanel: LinearLayout
    private var panelWhich = 0
    private var wrapBtn: Button? = null
    private var numBtn: Button? = null
    private lateinit var mainUpBtn: Button
    private lateinit var mainDownBtn: Button
    private lateinit var mainStartBtn: Button
    private lateinit var mainSpeedBtn: Button

    // find panel
    private lateinit var findEt: EditText
    private lateinit var replEt: EditText
    private lateinit var cbCase: CheckBox
    private lateinit var cbRegex: CheckBox
    private lateinit var cbWhole: CheckBox
    private lateinit var rbAll: RadioButton
    private lateinit var findStatus: TextView
    private lateinit var cbAlsoBm: CheckBox
    private val swatches = ArrayList<Button>()
    private var markColour = 0
    private var markSerial = 0
    @Volatile private var searching = false
    @Volatile private var searchCancel = false
    @Volatile var opCancel = false

    // tools panel
    private lateinit var gotoEt: EditText
    private lateinit var gotoStatus: TextView
    private lateinit var cpFromEt: EditText
    private lateinit var cpToEt: EditText
    private lateinit var cpStatus: TextView
    private lateinit var rrFromEt: EditText
    private lateinit var rrToEt: EditText
    private lateinit var rrTextEt: EditText
    private lateinit var rrStatus: TextView
    private lateinit var dirUpBtn: Button
    private lateinit var dirDownBtn: Button
    private lateinit var speedSb: SeekBar
    private lateinit var speedTv: TextView
    private lateinit var customEt: EditText
    private lateinit var scrollStatusTv: TextView
    private lateinit var scrollLineTv: TextView
    private lateinit var scmToggleBtn: Button
    private lateinit var scmFileTv: TextView
    private lateinit var scmStatusTv: TextView
    private lateinit var scmFromEt: EditText
    private lateinit var scmToEt: EditText

    // special copy mode
    var scmActive = false
    var scmStart = -1
    var scmEnd = -1
    var scmPane: Pane? = null
    var scmUri: Uri? = null
    private var pendingScmSave = false

    // delete lines panel
    private val delRows = ArrayList<DelRow>()
    private var delPane: Pane? = null
    private var delPickRowObj: DelRow? = null
    private var delPickStep = 0
    private lateinit var delPairsBox: LinearLayout
    private lateinit var delPasteEt: EditText
    private lateinit var delSummary: TextView
    private lateinit var delInstr: TextView

    // misc
    private var pendingNewTab = false
    private var pendingSavePane: Pane? = null
    private var pendingSaveThen: (() -> Unit)? = null
    private var busyTv: TextView? = null
    private var lastBusy = 0L
    private var statusPending = false

    // ───────── UI helpers ─────────
    private fun roundBg(color: Int, r: Int): GradientDrawable {
        val g = GradientDrawable()
        g.setColor(color)
        g.cornerRadius = dp(r).toFloat()
        return g
    }

    fun toast(s: String) { Toast.makeText(this, s, Toast.LENGTH_SHORT).show() }

    private fun mkBtn(text: String, bg: Int, fgc: Int, click: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.textSize = 11f
        b.setTextColor(fgc)
        b.background = roundBg(bg, 5)
        b.setPadding(dp(3), dp(3), dp(3), dp(3))
        b.minHeight = 0
        b.minimumHeight = 0
        b.minWidth = 0
        b.minimumWidth = 0
        b.maxLines = 1
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.setOnClickListener { click() }
        return b
    }

    private fun mkTv(text: String, color: Int, sp: Float): TextView {
        val t = TextView(this)
        t.text = text
        t.setTextColor(color)
        t.textSize = sp
        return t
    }

    private fun mkEt(hint: String, number: Boolean, widthDp: Int): EditText {
        val e = EditText(this)
        e.hint = hint
        e.textSize = 13f
        e.setTextColor(0xFF1A252F.toInt())
        e.setHintTextColor(0xFF7F8C8D.toInt())
        e.setBackgroundColor(0xFFECF0F1.toInt())
        e.setPadding(dp(6), dp(4), dp(6), dp(4))
        e.setSingleLine(true)
        if (number) e.inputType = InputType.TYPE_CLASS_NUMBER
        if (widthDp > 0) e.layoutParams = LinearLayout.LayoutParams(dp(widthDp), ViewGroup.LayoutParams.WRAP_CONTENT)
        return e
    }

    private fun lp(w: Int, h: Int, weight: Float, m: Int): LinearLayout.LayoutParams {
        val p = LinearLayout.LayoutParams(w, h, weight)
        p.setMargins(dp(m), dp(m), dp(m), dp(m))
        return p
    }

    private fun eqRow(vararg views: View): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        for (v in views) r.addView(v, lp(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f, 1))
        return r
    }

    private fun flowRow(): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        r.gravity = Gravity.CENTER_VERTICAL
        return r
    }

    private fun section(bg: Int): LinearLayout {
        val s = LinearLayout(this)
        s.orientation = LinearLayout.VERTICAL
        s.setBackgroundColor(bg)
        s.setPadding(dp(6), dp(6), dp(6), dp(6))
        val p = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        p.setMargins(0, 0, 0, dp(4))
        s.layoutParams = p
        return s
    }

    private fun addGap(row: LinearLayout, v: View, wDp: Int = 0) {
        val p = LinearLayout.LayoutParams(if (wDp > 0) dp(wDp) else ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        p.setMargins(dp(2), dp(1), dp(2), dp(1))
        row.addView(v, p)
    }

    fun busyDialog(msg: String): AlertDialog {
        val t = TextView(this)
        t.text = msg
        t.setPadding(dp(20), dp(16), dp(20), dp(16))
        busyTv = t
        val dlg = DBuilder(this).setTitle("Please wait").setView(t).setCancelable(false)
            .setNegativeButton("Cancel") { _, _ -> opCancel = true; searchCancel = true }.create()
        dlg.show()
        return dlg
    }

    fun busyUpdate(msg: String) {
        val now = System.currentTimeMillis()
        if (now - lastBusy < 150L) return
        lastBusy = now
        ui.post { busyTv?.text = msg }
    }

    fun runTask(msg: String, work: () -> Unit, done: (String?) -> Unit) {
        opCancel = false
        val dlg = busyDialog(msg)
        Thread {
            var err: String? = null
            try { work() } catch (e: Exception) { err = e.message ?: e.toString() }
            val fe = err
            ui.post {
                try { dlg.dismiss() } catch (e: Exception) { }
                done(fe)
            }
        }.start()
    }

    // ───────── lifecycle ─────────
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        gDensity = resources.displayMetrics.density
        window.statusBarColor = cBg
        window.navigationBarColor = cBg
        buildUi()
        restoreSession()
        if (panes.isEmpty()) newPane()
        cleanWork()
        ui.postDelayed(autoSaveRun, 5000)
        handleViewIntent(intent)
    }

    override fun onNewIntent(intent: Intent?) {
        super.onNewIntent(intent)
        if (intent != null) handleViewIntent(intent)
    }

    private fun handleViewIntent(i: Intent) {
        val u = i.data
        if (i.action == Intent.ACTION_VIEW && u != null) {
            persist(u)
            val p = newPane()
            loadUri(p, u)
        }
    }

    private val autoSaveRun: Runnable = object : Runnable {
        override fun run() {
            if (sessionDirty) {
                saveSessionNow(false)
                autosaveTv.text = "💾 Saving…"
                autosaveTv.setTextColor(0xFFE67E22.toInt())
                ui.postDelayed({
                    autosaveTv.text = "💾 Auto-saved"
                    autosaveTv.setTextColor(0xFF27AE60.toInt())
                }, 600)
            }
            ui.postDelayed(this, 5000)
        }
    }

    override fun onPause() {
        super.onPause()
        saveSessionNow(true)
    }

    override fun onResume() {
        super.onResume()
        if (overlayOn) {
            if (skipAutoDock) skipAutoDock = false else exitFloat(false)
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        killOverlay()
        for (p in panes) { p.stopScroll(); p.doc.close() }
    }

    @Suppress("DEPRECATION")
    override fun onBackPressed() {
        if (panelWhich != 0) { showPanel(0); return }
        super.onBackPressed()
    }

    // ───────── UI build ─────────
    private fun buildUi() {
        root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(cBg)

        tabScroll = HorizontalScrollView(this)
        tabScroll.setBackgroundColor(0xFF252525.toInt())
        tabScroll.isHorizontalScrollBarEnabled = false
        tabStrip = LinearLayout(this)
        tabStrip.orientation = LinearLayout.HORIZONTAL
        tabScroll.addView(tabStrip, ViewGroup.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        root.addView(tabScroll, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        val tb = LinearLayout(this)
        tb.orientation = LinearLayout.VERTICAL
        tb.setBackgroundColor(cBar)
        tb.setPadding(dp(2), dp(2), dp(2), dp(2))
        toolbarBox = tb
        val g = 0xFF3C3C3C.toInt()
        tb.addView(eqRow(
            mkBtn("📄 New", g, cWhite) { newPane() },
            mkBtn("📂 Open", g, cWhite) { openFiles(false) },
            mkBtn("💾 Save", g, cWhite) { cur?.let { savePane(it, null) } },
            mkBtn("↩ Undo", g, cWhite) { cur?.view?.doUndo() },
            mkBtn("↪ Redo", g, cWhite) { cur?.view?.doRedo() },
            mkBtn("🔍 Find", 0xFF2980B9.toInt(), cWhite) { showPanel(1) }))
        tb.addView(eqRow(
            mkBtn("✂ DelLines", 0xFF5C1A1A.toInt(), cWhite) { openDelPanel() },
            mkBtn("🔗 BlankLn", 0xFF1A3A5C.toInt(), cWhite) { removeBlankDialog() },
            mkBtn("🔵 Marks", 0xFF2E3A2E.toInt(), 0xFF7FFFB2.toInt()) { showBookmarks() },
            mkBtn("✖ Close", 0xFF4A4A4A.toInt(), 0xFFFFAAAA.toInt()) { closeCurrentTab() },
            mkBtn("🛠 Tools", 0xFF4A3A6A.toInt(), 0xFFD8B8FF.toInt()) { showPanel(2) },
            mkBtn("📌 Float", 0xFF1F6F5C.toInt(), cWhite) { toggleFloat() },
            mkBtn("⋮ Menu", g, cWhite) { showMenu() }))
        val wb = mkBtn("↩ Wrap", g, cWhite) { toggleWrap() }
        wrapBtn = wb
        tb.addView(eqRow(
            mkBtn("✂ Cut", g, cWhite) { cur?.view?.copySel(true) },
            mkBtn("📋 Copy", g, cWhite) { cur?.view?.copySel(false) },
            mkBtn("📥 Paste", g, cWhite) { cur?.view?.paste() },
            mkBtn("Sel All", g, cWhite) { cur?.view?.selectAll() },
            wb,
            mkBtn("A−", g, cWhite) { zoomBy(-1) },
            mkBtn("A+", g, cWhite) { zoomBy(1) }))
        mainUpBtn = mkBtn("▲ Up", 0xFF2980B9.toInt(), cWhite) { setDir("up") }
        mainDownBtn = mkBtn("▼ Down", 0xFF2980B9.toInt(), cWhite) { setDir("down") }
        mainStartBtn = mkBtn("▶ Scroll", 0xFF27AE60.toInt(), cWhite) { toggleAutoScroll() }
        mainSpeedBtn = mkBtn("3.0/s", 0xFF3C3C3C.toInt(), 0xFFF0D060.toInt()) { speedDialog() }
        tb.addView(eqRow(
            mainUpBtn, mainDownBtn, mainStartBtn,
            mkBtn("−", g, cWhite) { bumpSpeed(1.0 / 1.3) },
            mainSpeedBtn,
            mkBtn("+", g, cWhite) { bumpSpeed(1.3) }))
        root.addView(tb, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        val sr = LinearLayout(this)
        sr.orientation = LinearLayout.HORIZONTAL
        sr.setBackgroundColor(0xFF007ACC.toInt())
        sr.setPadding(dp(6), dp(2), dp(6), dp(2))
        statusTv = mkTv("Ln 1/1, Col 1", cWhite, 11f)
        statusTv.setSingleLine(true)
        statusTv.setOnClickListener { cur?.let { copyLineNumber(it, it.view.caretL) } }
        autosaveTv = mkTv("💾 Auto-saved", 0xFF90EE90.toInt(), 10f)
        sr.addView(statusTv, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        val nb = mkBtn("# ✓", 0xFF1A5C8A.toInt(), cWhite) { toggleNums() }
        numBtn = nb
        sr.addView(nb, lp(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, 0f, 1))
        sr.addView(autosaveTv, LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        root.addView(sr, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        panelScroll = MaxHeightScroll(this)
        panelScroll.setBackgroundColor(0xFF161616.toInt())
        panelScroll.visibility = View.GONE
        val holder = LinearLayout(this)
        holder.orientation = LinearLayout.VERTICAL
        findPanel = buildFindPanel()
        toolsPanel = buildToolsPanel()
        delPanel = buildDelPanel()
        holder.addView(findPanel)
        holder.addView(toolsPanel)
        holder.addView(delPanel)
        panelScroll.addView(holder, ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        root.addView(panelScroll, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        editorHost = FrameLayout(this)
        editorHost.setBackgroundColor(cBg)
        root.addView(editorHost, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
        setContentView(root)
        showPanel(0)
    }

    fun showPanel(which: Int) {
        val w = if (which == panelWhich && which != 0) 0 else which
        panelWhich = w
        findPanel.visibility = if (w == 1) View.VISIBLE else View.GONE
        toolsPanel.visibility = if (w == 2) View.VISIBLE else View.GONE
        delPanel.visibility = if (w == 3) View.VISIBLE else View.GONE
        panelScroll.visibility = if (w == 0) View.GONE else View.VISIBLE
        if (w == 2) syncScrollUi()
        if (w != 3) { delPickStep = 0; delPane?.view?.delPreview = null; delPane?.view?.invalidate() }
        if (w == 1) { findEt.requestFocus() }
    }

    private fun closeBtnRow(): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        val b = mkBtn("✖ Close panel", 0xFF566573.toInt(), cWhite) { showPanel(0) }
        r.addView(b, lp(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, 0f, 2))
        return r
    }

    // ───────── Find panel ─────────
    private fun buildFindPanel(): LinearLayout {
        val p = LinearLayout(this)
        p.orientation = LinearLayout.VERTICAL
        p.setBackgroundColor(0xFF1E1E1E.toInt())
        p.setPadding(dp(6), dp(6), dp(6), dp(6))
        val r0 = flowRow()
        addGap(r0, mkTv("Find:", cTxt, 12f))
        findEt = mkEt("text to find", false, 0)
        r0.addView(findEt, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        p.addView(r0)
        val r1 = flowRow()
        addGap(r1, mkTv("Replace:", cTxt, 12f))
        replEt = mkEt("replacement", false, 0)
        r1.addView(replEt, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        p.addView(r1)
        val r2 = flowRow()
        cbCase = CheckBox(this); cbCase.text = "Match case"
        cbRegex = CheckBox(this); cbRegex.text = "Regex"
        cbWhole = CheckBox(this); cbWhole.text = "Whole word"
        for (c in listOf(cbCase, cbRegex, cbWhole)) { c.setTextColor(cTxt); c.textSize = 12f; r2.addView(c) }
        p.addView(r2)
        val r3 = flowRow()
        r3.setBackgroundColor(0xFF16324A.toInt())
        addGap(r3, mkTv(" Replace All scope:", 0xFFA0C8FF.toInt(), 12f))
        val rg = RadioGroup(this)
        rg.orientation = RadioGroup.HORIZONTAL
        val rbCur = RadioButton(this); rbCur.text = "Current Tab"; rbCur.id = View.generateViewId()
        rbAll = RadioButton(this); rbAll.text = "All Opened Tabs"; rbAll.id = View.generateViewId()
        rbCur.setTextColor(0xFFA0C8FF.toInt()); rbAll.setTextColor(0xFF7FFFB2.toInt())
        rbCur.textSize = 12f; rbAll.textSize = 12f
        rg.addView(rbCur); rg.addView(rbAll)
        rg.check(rbCur.id)
        r3.addView(rg)
        p.addView(r3)
        p.addView(eqRow(
            mkBtn("Find Next", 0xFF2980B9.toInt(), cWhite) { doFind(true) },
            mkBtn("Find Prev", 0xFF1F618D.toInt(), cWhite) { doFind(false) },
            mkBtn("Replace", 0xFF27AE60.toInt(), cWhite) { replaceOne() },
            mkBtn("Replace All", 0xFF1E8449.toInt(), cWhite) { replaceAll() }))
        val mk = flowRow()
        mk.setBackgroundColor(0xFF252525.toInt())
        addGap(mk, mkTv(" Mark All:", 0xFFF39C12.toInt(), 12f))
        for (i in MARK_COLOURS.indices) {
            val sw = mkBtn(if (i == 0) "✓" else "", MARK_COLOURS[i], 0xFF000000.toInt()) { setMarkColour(i) }
            swatches.add(sw)
            addGap(mk, sw, 30)
        }
        p.addView(mk)
        val mb = flowRow()
        cbAlsoBm = CheckBox(this); cbAlsoBm.text = "🔵 Also bookmark"; cbAlsoBm.isChecked = true
        cbAlsoBm.setTextColor(0xFF7FFFB2.toInt()); cbAlsoBm.textSize = 12f
        mb.addView(cbAlsoBm)
        p.addView(mb)
        p.addView(eqRow(
            mkBtn("✦ Mark All", 0xFFE67E22.toInt(), cWhite) { markAll() },
            mkBtn("✖ Clear Marks", 0xFF7F8C8D.toInt(), cWhite) { clearMarks() },
            mkBtn("✖✖ Clear All", 0xFF5A3A3A.toInt(), 0xFFFFAAAA.toInt()) { clearMarks() }))
        findStatus = mkTv("", 0xFF2ECC71.toInt(), 12f)
        p.addView(findStatus)
        p.addView(eqRow(
            mkBtn("■ Stop search", 0xFFC0392B.toInt(), cWhite) { searchCancel = true },
            mkBtn("✖ Close", 0xFF566573.toInt(), cWhite) { showPanel(0) }))
        return p
    }

    private fun setMarkColour(i: Int) {
        markColour = i
        for (k in swatches.indices) swatches[k].text = if (k == i) "✓" else ""
    }

    private fun setFindStatus(s: String, color: Int) {
        findStatus.text = s
        findStatus.setTextColor(color)
    }

    // ───────── Tools panel ─────────
    private fun buildToolsPanel(): LinearLayout {
        val p = LinearLayout(this)
        p.orientation = LinearLayout.VERTICAL
        p.setPadding(dp(4), dp(4), dp(4), dp(4))
        p.addView(closeBtnRow())

        // go to line
        val gs = section(0xFF1A252F.toInt())
        val g1 = flowRow()
        addGap(g1, mkTv("Go to Line:", 0xFFECF0F1.toInt(), 12f))
        gotoEt = mkEt("line", true, 90)
        gotoEt.setOnEditorActionListener { _, _, _ -> doGoto(); true }
        addGap(g1, gotoEt, 90)
        addGap(g1, mkBtn("Go", 0xFF27AE60.toInt(), cWhite) { doGoto() })
        gotoStatus = mkTv("", 0xFFF39C12.toInt(), 12f)
        addGap(g1, gotoStatus)
        gs.addView(g1)
        p.addView(gs)

        // copy lines
        val cs = section(0xFF1B3A4B.toInt())
        val c1 = flowRow()
        addGap(c1, mkTv("📋 Copy Lines  From:", 0xFFECF0F1.toInt(), 12f))
        cpFromEt = mkEt("from", true, 70)
        addGap(c1, cpFromEt, 70)
        addGap(c1, mkTv("To:", 0xFFBDC3C7.toInt(), 12f))
        cpToEt = mkEt("to", true, 70)
        addGap(c1, cpToEt, 70)
        cs.addView(c1)
        cs.addView(eqRow(
            mkBtn("📋 Copy", 0xFF2980B9.toInt(), cWhite) { copyRange() },
            mkBtn("👁 Highlight", 0xFF8E44AD.toInt(), cWhite) { highlightCopyRange() },
            mkBtn("✖ Clear", 0xFF566573.toInt(), cWhite) { clearCopyRange() }))
        cpStatus = mkTv("", 0xFFF39C12.toInt(), 12f)
        cs.addView(cpStatus)
        p.addView(cs)

        // replace lines
        val rs = section(0xFF2E4A1E.toInt())
        val r1 = flowRow()
        addGap(r1, mkTv("✏ Replace Lines  From:", 0xFFECF0F1.toInt(), 12f))
        rrFromEt = mkEt("from", true, 70)
        addGap(r1, rrFromEt, 70)
        addGap(r1, mkTv("To:", 0xFFBDC3C7.toInt(), 12f))
        rrToEt = mkEt("to", true, 70)
        addGap(r1, rrToEt, 70)
        rs.addView(r1)
        rrTextEt = EditText(this)
        rrTextEt.hint = "Replacement text"
        rrTextEt.minLines = 3
        rrTextEt.gravity = Gravity.TOP
        rrTextEt.setTextColor(cTxt)
        rrTextEt.setHintTextColor(0xFF888888.toInt())
        rrTextEt.setBackgroundColor(0xFF2A2A2A.toInt())
        rrTextEt.textSize = 13f
        rrTextEt.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
        rs.addView(rrTextEt, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        rs.addView(eqRow(
            mkBtn("✏ Replace", 0xFF27AE60.toInt(), cWhite) { replaceRange() },
            mkBtn("👁 Preview", 0xFF8E44AD.toInt(), cWhite) { previewReplaceRange() },
            mkBtn("✖ Clear", 0xFF566573.toInt(), cWhite) { clearReplaceRange() }))
        rrStatus = mkTv("", 0xFFF39C12.toInt(), 12f)
        rs.addView(rrStatus)
        p.addView(rs)

        // auto scroll
        val ss = section(0xFF2C3E50.toInt())
        ss.addView(mkTv("AUTO-SCROLL  (keys U / D = direction)", cWhite, 12f))
        dirUpBtn = mkBtn("▲ Up (U)", 0xFF2980B9.toInt(), cWhite) { setDir("up") }
        dirDownBtn = mkBtn("▼ Down (D)", 0xFF2980B9.toInt(), cWhite) { setDir("down") }
        ss.addView(eqRow(dirUpBtn, dirDownBtn))
        speedSb = SeekBar(this)
        speedSb.max = 1000
        speedSb.progress = 15
        speedSb.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar?, progress: Int, fromUser: Boolean) {
                if (!fromUser) return
                val v = 0.01 + progress / 1000.0 * 199.99
                val pn = cur ?: return
                pn.speed = v
                speedTv.text = String.format("%.2f lines/s", v)
                sessionDirty = true
            }
            override fun onStartTrackingTouch(sb: SeekBar?) { }
            override fun onStopTrackingTouch(sb: SeekBar?) { }
        })
        ss.addView(speedSb, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        val sp = flowRow()
        addGap(sp, mkTv("Speed:", cWhite, 12f))
        speedTv = mkTv("3.00 lines/s", 0xFFF0F0F0.toInt(), 12f)
        addGap(sp, speedTv)
        addGap(sp, mkTv(" Custom:", cWhite, 12f))
        customEt = mkEt("3", false, 70)
        customEt.inputType = InputType.TYPE_CLASS_NUMBER or InputType.TYPE_NUMBER_FLAG_DECIMAL
        customEt.setText("3")
        addGap(sp, customEt, 70)
        addGap(sp, mkBtn("Set", 0xFF8E44AD.toInt(), cWhite) { applyCustomSpeed() })
        ss.addView(sp)
        ss.addView(eqRow(
            mkBtn("▶ Scroll Start", 0xFF27AE60.toInt(), cWhite) { cur?.startScroll(); syncScrollUi() },
            mkBtn("■ Scroll Stop", 0xFFC0392B.toInt(), cWhite) { cur?.stopScroll(); syncScrollUi(); scrollLineTv.text = "📍 Line: —" }))
        scrollStatusTv = mkTv("● Stopped", 0xFFE74C3C.toInt(), 12f)
        scrollLineTv = mkTv("📍 Line: —", 0xFFF39C12.toInt(), 12f)
        val sl = flowRow()
        addGap(sl, scrollStatusTv)
        addGap(sl, mkTv("   ", cWhite, 12f))
        addGap(sl, scrollLineTv)
        ss.addView(sl)
        p.addView(ss)

        // special copy mode
        val ms = section(0xFF1A0A2E.toInt())
        scmToggleBtn = mkBtn("📌 Special Copy Mode: OFF", 0xFF4A235A.toInt(), cWhite) { toggleScm() }
        ms.addView(scmToggleBtn, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        val sm = flowRow()
        addGap(sm, mkTv("Lines  From:", 0xFFECF0F1.toInt(), 12f))
        scmFromEt = mkEt("from", true, 70)
        addGap(sm, scmFromEt, 70)
        addGap(sm, mkTv("To:", 0xFFBDC3C7.toInt(), 12f))
        scmToEt = mkEt("to", true, 70)
        addGap(sm, scmToEt, 70)
        addGap(sm, mkBtn("✔ Select", 0xFF8E44AD.toInt(), cWhite) { scmSelectManual() })
        ms.addView(sm)
        ms.addView(eqRow(
            mkBtn("📁 Choose Output File", 0xFF2E4057.toInt(), cWhite) { scmChooseFile() },
            mkBtn("✖ Clear File", 0xFF566573.toInt(), cWhite) { scmClearFile() }))
        ms.addView(eqRow(
            mkBtn("S  Save range", 0xFF27AE60.toInt(), cWhite) { scmSave() },
            mkBtn("R  Clear selection", 0xFFC0392B.toInt(), cWhite) { scmClearSel() }))
        scmFileTv = mkTv("No file chosen", 0xFF7F8C8D.toInt(), 12f)
        scmStatusTv = mkTv("Enable mode → tap START line → tap END line → press S (or the Save button)", 0xFF7F8C8D.toInt(), 12f)
        ms.addView(scmFileTv)
        ms.addView(scmStatusTv)
        p.addView(ms)
        return p
    }

    // ───────── Delete-lines panel ─────────
    private fun buildDelPanel(): LinearLayout {
        val p = LinearLayout(this)
        p.orientation = LinearLayout.VERTICAL
        p.setBackgroundColor(0xFFECF0F1.toInt())
        p.setPadding(dp(6), dp(6), dp(6), dp(6))
        p.addView(mkTv("✂  Delete Lines — Multiple Pairs", 0xFF2C3E50.toInt(), 14f))
        delInstr = mkTv("Add pairs below, then press DELETE ALL to remove all selected ranges.", 0xFF2C3E50.toInt(), 12f)
        p.addView(delInstr)
        p.addView(mkTv("📋 Paste line pairs (one per line, e.g. \"12 15\", \"12-15\" or \"12,15\"):", 0xFF2C3E50.toInt(), 12f))
        delPasteEt = EditText(this)
        delPasteEt.minLines = 3
        delPasteEt.gravity = Gravity.TOP
        delPasteEt.textSize = 13f
        delPasteEt.setTextColor(0xFF111111.toInt())
        delPasteEt.setBackgroundColor(0xFFFFFFFF.toInt())
        delPasteEt.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
        p.addView(delPasteEt, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        p.addView(eqRow(
            mkBtn("🗑 DELETE ALL (pasted)", 0xFFC0392B.toInt(), cWhite) { deleteFromPaste() },
            mkBtn("👁 Preview Pasted", 0xFF27AE60.toInt(), cWhite) { previewFromPaste() },
            mkBtn("✖ Clear", 0xFF7F8C8D.toInt(), cWhite) { delPasteEt.setText("") }))
        p.addView(mkTv("— or build pairs manually below —", 0xFF7F8C8D.toInt(), 11f))
        delPairsBox = LinearLayout(this)
        delPairsBox.orientation = LinearLayout.VERTICAL
        p.addView(delPairsBox)
        p.addView(eqRow(
            mkBtn("➕ Add Pair", 0xFF2980B9.toInt(), cWhite) { addDelRow() },
            mkBtn("🗑 DELETE ALL", 0xFFC0392B.toInt(), cWhite) { deleteAllPairs() },
            mkBtn("👁 Preview", 0xFF27AE60.toInt(), cWhite) { previewAllPairs() },
            mkBtn("✖ Cancel", 0xFF7F8C8D.toInt(), cWhite) { showPanel(0) }))
        delSummary = mkTv("", 0xFFE67E22.toInt(), 12f)
        p.addView(delSummary)
        return p
    }

    // ───────── panes / tabs ─────────
    fun newPane(): Pane {
        counter++
        val p = Pane(this, counter)
        p.view = EditorView(this, p, this)
        panes.add(p)
        selectPane(p)
        return p
    }

    fun selectPane(p: Pane) {
        cur = p
        editorHost.removeAllViews()
        val parent = p.view.parent
        if (parent is ViewGroup) parent.removeView(p.view)
        editorHost.addView(p.view, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))
        p.view.requestFocus()
        refreshTabs()
        updateStatus()
        syncScrollUi()
        wrapBtn?.text = if (p.view.wrap) "↩ Wrap ✓" else "↩ Wrap"
        syncNumBtn()
        if (delPane != null && delPane !== p && panelWhich == 3) showPanel(0)
        sessionDirty = true
    }

    fun refreshTabs() {
        tabStrip.removeAllViews()
        for (p in panes) {
            val sel = p === cur
            val b = Button(this)
            b.text = p.label()
            b.isAllCaps = false
            b.textSize = 12f
            b.setTextColor(if (sel) 0xFFF1C40F.toInt() else cTxt)
            b.setBackgroundColor(if (sel) cBg else 0xFF2D2D2D.toInt())
            b.minHeight = 0; b.minimumHeight = 0; b.minWidth = 0; b.minimumWidth = 0
            b.setPadding(dp(12), dp(6), dp(12), dp(6))
            b.isFocusable = false
            b.isFocusableInTouchMode = false
            b.setOnClickListener { selectPane(p) }
            tabStrip.addView(b, lp(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, 0f, 1))
        }
    }

    fun closeCurrentTab() {
        val p = cur ?: return
        confirmUnsaved(p) {
            if (panes.size == 1) {
                p.stopScroll()
                p.clearKept()
                val old = p.doc
                p.replaceDoc(Doc())
                p.fileName = ""
                p.bookmarks.clear()
                p.rebuildBm()
                p.view.caretL = 0; p.view.caretC = 0; p.view.ancL = 0; p.view.ancC = 0
                p.view.topLine = 0; p.view.topPx = 0f
                p.view.clearOverlays()
                if (old.srcKind == "file") { try { File(old.srcRef).delete() } catch (e: Exception) { } }
                refreshTabs(); updateStatus(); p.view.invalidate()
            } else {
                val i = panes.indexOf(p)
                p.closePane()
                panes.remove(p)
                selectPane(panes[minOf(i, panes.size - 1)])
            }
            sessionDirty = true
        }
    }

    fun nextTab(d: Int) {
        if (panes.size < 2) return
        val i = panes.indexOf(cur)
        selectPane(panes[(i + d + panes.size) % panes.size])
    }

    fun confirmUnsaved(p: Pane, proceed: () -> Unit) {
        if (!p.doc.modified) { proceed(); return }
        DBuilder(this).setTitle("Unsaved Changes")
            .setMessage("Save changes to '" + p.label().trimStart('*') + "' before continuing?")
            .setPositiveButton("Save") { _, _ -> savePane(p) { proceed() } }
            .setNegativeButton("Don't save") { _, _ -> proceed() }
            .setNeutralButton("Cancel", null).show()
    }

    // ───────── status ─────────
    fun onViewChanged(p: Pane) {
        sessionDirty = true
        if (p === cur) statusSoon()
    }

    fun onEdited(p: Pane) {
        if (scmPane === p && scmStart >= 0) { scmStart = -1; scmEnd = -1 }
        sessionDirty = true
        if (p === cur) statusSoon()
    }

    fun onIndexProgress(p: Pane) {
        p.view.invalidate()
        if (p === cur) updateStatus()
    }

    private fun statusSoon() {
        if (statusPending) return
        statusPending = true
        ui.postDelayed({ statusPending = false; updateStatus() }, 50)
    }

    fun updateStatus() {
        val p = cur ?: return
        val v = p.view
        val d = p.doc
        val tot = d.total
        val sb = StringBuilder()
        sb.append("Ln ").append(v.caretL + 1).append("/").append(tot).append(", Col ").append(v.caretC + 1)
        sb.append("  |  ").append(p.label())
        val sz = d.src?.size ?: 0L
        if (sz > 0L) sb.append("  |  ").append(fmtSize(sz))
        if (d.indexing) {
            val pct = if (sz > 0L) (d.indexedBytes * 100L / sz) else 0L
            sb.append("  |  ⏳ Indexing ").append(pct).append("% (read-only until done)")
        } else if (sz <= 2000000L && tot <= 60000) {
            if (p.wcVer != d.version) {
                var words = 0
                var chars = 0
                for (i in 0 until tot) {
                    val t = d.getLine(i)
                    chars += t.length + 1
                    var inW = false
                    for (ch in t) {
                        if (ch.isWhitespace()) inW = false else if (!inW) { inW = true; words++ }
                    }
                }
                p.wcVer = d.version; p.wcWords = words; p.wcChars = maxOf(0, chars - 1)
            }
            sb.append("  |  Words: ").append(p.wcWords).append("  Chars: ").append(p.wcChars)
        }
        statusTv.text = sb.toString()
    }

    fun zoomBy(delta: Int) {
        val v = cur?.view ?: return
        v.fontSize = (v.fontSize + delta).coerceIn(6, 72)
        v.applyFont()
        sessionDirty = true
    }

    private fun toggleWrap() {
        val p = cur ?: return
        val v = p.view
        v.wrap = !v.wrap
        v.topPx = 0f
        v.hx = 0f
        v.invalidate()
        wrapBtn?.text = if (v.wrap) "↩ Wrap ✓" else "↩ Wrap"
        sessionDirty = true
    }

    fun toggleNums() {
        val p = cur ?: return
        p.view.showNums = !p.view.showNums
        p.view.invalidate()
        syncNumBtn()
        sessionDirty = true
        toast(if (p.view.showNums) "Line numbers shown" else "Line numbers hidden")
    }

    private fun syncNumBtn() {
        val p = cur ?: return
        numBtn?.text = if (p.view.showNums) "# ✓" else "# ✕"
    }

    fun copyLineNumber(p: Pane, line: Int) {
        val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        cm.setPrimaryClip(ClipData.newPlainText("line", (line + 1).toString()))
        toast("📋 Copied line ${line + 1}")
    }

    // ───────── taps from the editor ─────────
    fun preChar(p: Pane, ch: Char): Boolean {
        val c = ch.lowercaseChar()
        if (scmActive && scmPane === p && scmStart >= 0) {
            if (c == 's') { scmSave(); return true }
            if (c == 'r') { scmClearSel(); return true }
        }
        if (c == 'u') { p.dir = "up"; syncScrollUi() } else if (c == 'd') { p.dir = "down"; syncScrollUi() }
        return false
    }

    /** returns true if no soft keyboard should be shown */
    fun onTextTap(p: Pane, line: Int): Boolean {
        if (delPickStep != 0 && delPane === p && panelWhich == 3) { delStoreLine(line + 1); return true }
        if (scmActive) { scmPane = p; scmOnClick(p, line); return true }
        return false
    }

    fun onNumberTap(p: Pane, line: Int): Boolean {
        if (delPickStep != 0 && delPane === p && panelWhich == 3) { delStoreLine(line + 1); return true }
        if (scmActive) { scmPane = p; scmOnClick(p, line); return true }
        return false
    }

    fun onAutoScrollTick(p: Pane) {
        if (p === cur && panelWhich == 2) {
            scrollLineTv.text = "📍 Line: ${p.view.topLine + 1} / ${p.doc.total}"
        }
    }

    // ───────── auto-scroll / go to / ranges ─────────
    fun syncScrollUi() {
        val p = cur ?: return
        if (!::speedSb.isInitialized) return
        mainUpBtn.background = roundBg(if (p.dir == "up") 0xFF27AE60.toInt() else 0xFF2980B9.toInt(), 5)
        mainDownBtn.background = roundBg(if (p.dir == "down") 0xFF27AE60.toInt() else 0xFF2980B9.toInt(), 5)
        mainStartBtn.text = if (p.scrollActive) "■ Stop" else "▶ Scroll"
        mainStartBtn.background = roundBg(if (p.scrollActive) 0xFFC0392B.toInt() else 0xFF27AE60.toInt(), 5)
        mainSpeedBtn.text = if (p.speed >= 100.0) String.format("%.0f/s", p.speed) else String.format("%.1f/s", p.speed)
        dirUpBtn.background = roundBg(if (p.dir == "up") 0xFF27AE60.toInt() else 0xFF2980B9.toInt(), 5)
        dirDownBtn.background = roundBg(if (p.dir == "down") 0xFF27AE60.toInt() else 0xFF2980B9.toInt(), 5)
        speedSb.progress = (((p.speed - 0.01) / 199.99) * 1000.0).toInt().coerceIn(0, 1000)
        speedTv.text = String.format("%.2f lines/s", p.speed)
        if (p.scrollActive) {
            scrollStatusTv.text = "● Scrolling " + p.dir
            scrollStatusTv.setTextColor(0xFF2ECC71.toInt())
        } else {
            scrollStatusTv.text = "● Stopped"
            scrollStatusTv.setTextColor(0xFFE74C3C.toInt())
        }
    }

    private fun toggleAutoScroll() {
        val p = cur ?: return
        if (p.scrollActive) p.stopScroll() else p.startScroll()
        syncScrollUi()
    }

    private fun bumpSpeed(f: Double) {
        val p = cur ?: return
        p.speed = (p.speed * f).coerceIn(0.01, 10000.0)
        sessionDirty = true
        syncScrollUi()
    }

    private fun speedDialog() {
        val p = cur ?: return
        inputDialog("Scroll speed (lines per second)", String.format("%.2f", p.speed)) { s ->
            val v = s.trim().toDoubleOrNull()
            if (v == null || v <= 0.0 || v > 10000.0) toast("Enter a speed between 0.01 and 10000")
            else { p.speed = v; sessionDirty = true; syncScrollUi() }
        }
    }

    private fun setDir(d: String) {
        val p = cur ?: return
        p.dir = d
        syncScrollUi()
    }

    private fun applyCustomSpeed() {
        val p = cur ?: return
        val v = customEt.text.toString().trim().toDoubleOrNull()
        if (v == null || v <= 0.0 || v > 10000.0) { toast("Enter a speed between 0.01 and 10000"); return }
        p.speed = v
        syncScrollUi()
        speedTv.text = String.format("%.2f lines/s", v)
        sessionDirty = true
    }

    fun focusGoto() {
        if (panelWhich != 2) showPanel(2)
        gotoEt.requestFocus()
        gotoEt.selectAll()
    }

    private fun doGoto() {
        val p = cur ?: return
        val n = gotoEt.text.toString().trim().toIntOrNull()
        if (n == null) { gotoStatus.text = "⚠ Enter a number"; return }
        val tot = p.doc.total
        if (n < 1 || n > tot) { gotoStatus.text = "⚠ 1 – $tot"; return }
        p.view.setCaret(n - 1, 0, false)
        p.view.scrollToLine(n - 1, true)
        gotoStatus.text = "✔ Line $n"
        p.view.requestFocus()
    }

    private fun parseRange(fromEt: EditText, toEt: EditText, st: TextView, tot: Int): IntArray? {
        val f = fromEt.text.toString().trim().toIntOrNull()
        val t = toEt.text.toString().trim().toIntOrNull()
        if (f == null || t == null) { st.text = "⚠ Enter both line numbers"; return null }
        val a = minOf(f, t)
        val b = maxOf(f, t)
        if (a < 1 || b > tot) { st.text = "⚠ Lines must be within 1 – $tot"; return null }
        return intArrayOf(a, b)
    }

    private fun copyRange() {
        val p = cur ?: return
        val r = parseRange(cpFromEt, cpToEt, cpStatus, p.doc.total) ?: return
        val last = p.doc.getLine(r[1] - 1)
        val text = p.doc.getText(r[0] - 1, 0, r[1] - 1, last.length, 900000)
        if (text == null) { cpStatus.text = "⚠ Too large for the clipboard — use Special Copy Mode"; return }
        val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        cm.setPrimaryClip(ClipData.newPlainText("lines", text))
        cpStatus.text = "✔ Copied lines ${r[0]}–${r[1]} (${r[1] - r[0] + 1} lines)"
        highlightCopyRange()
    }

    private fun highlightCopyRange() {
        val p = cur ?: return
        val r = parseRange(cpFromEt, cpToEt, cpStatus, p.doc.total) ?: return
        val arr = intArrayOf(r[0] - 1, r[1] - 1)
        p.view.copyHl = arr
        p.view.scrollToLine(r[0] - 1, false)
        p.view.invalidate()
        ui.postDelayed({ if (p.view.copyHl === arr) { p.view.copyHl = null; p.view.invalidate() } }, 4000)
    }

    private fun clearCopyRange() {
        cur?.view?.copyHl = null
        cur?.view?.invalidate()
        cpFromEt.setText(""); cpToEt.setText(""); cpStatus.text = ""
    }

    private fun previewReplaceRange() {
        val p = cur ?: return
        val r = parseRange(rrFromEt, rrToEt, rrStatus, p.doc.total) ?: return
        p.view.rrHl = intArrayOf(r[0] - 1, r[1] - 1)
        p.view.scrollToLine(r[0] - 1, false)
        p.view.invalidate()
        rrStatus.text = "👁 Lines ${r[0]}–${r[1]} will be replaced"
    }

    private fun clearReplaceRange() {
        cur?.view?.rrHl = null
        cur?.view?.invalidate()
        rrFromEt.setText(""); rrToEt.setText(""); rrTextEt.setText(""); rrStatus.text = ""
    }

    private fun replaceRange() {
        val p = cur ?: return
        if (p.doc.indexing) { toast("Still indexing — try again in a moment"); return }
        val r = parseRange(rrFromEt, rrToEt, rrStatus, p.doc.total) ?: return
        val txt = rrTextEt.text.toString()
        DBuilder(this).setTitle("Replace lines")
            .setMessage("Replace lines ${r[0]}–${r[1]} with the new text?")
            .setPositiveButton("Replace") { _, _ ->
                val v = p.view
                p.doc.edit(r[0] - 1, r[1], txt.replace("\r\n", "\n").split("\n").toTypedArray(), v.caretL, v.caretC, null)
                v.caretL = r[0] - 1; v.caretC = 0; v.ancL = v.caretL; v.ancC = 0
                v.afterEdit()
                rrStatus.text = "✔ Replaced lines ${r[0]}–${r[1]}"
            }.setNegativeButton("Cancel", null).show()
    }

    // ───────── bookmarks ─────────
    private fun inputDialog(title: String, initial: String, ok: (String) -> Unit) {
        val et = EditText(this)
        et.setText(initial)
        et.setSingleLine(true)
        et.setSelection(initial.length)
        DBuilder(this).setTitle(title).setView(et)
            .setPositiveButton("OK") { _, _ -> ok(et.text.toString()) }
            .setNegativeButton("Cancel", null).show()
    }

    fun toggleBookmarkAt(p: Pane, line: Int) {
        val ex = p.bookmarks.firstOrNull { it.line == line }
        if (ex != null) {
            p.bookmarks.remove(ex)
            p.rebuildBm()
            sessionDirty = true
            return
        }
        var def = p.doc.getLine(line).trim()
        if (def.length > 40) def = def.substring(0, 40)
        if (def.isEmpty()) def = "Line ${line + 1}"
        p.bookmarks.add(Bm(line, def))
        p.rebuildBm()
        sessionDirty = true
    }

    fun bmNext(forward: Boolean) {
        val p = cur ?: return
        if (p.bookmarks.isEmpty()) { toast("No bookmarks in this tab"); return }
        val sorted = p.bookmarks.sortedBy { it.line }
        val c = p.view.caretL
        val target: Bm = if (forward) (sorted.firstOrNull { it.line > c } ?: sorted[0])
        else (sorted.lastOrNull { it.line < c } ?: sorted[sorted.size - 1])
        p.view.setCaret(target.line, 0, false)
        p.view.scrollToLine(target.line, false)
    }

    fun showBookmarks() {
        val p = cur ?: return
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        val sv = ScrollView(this)
        sv.addView(box)
        val dref = arrayOfNulls<AlertDialog>(1)
        fun fill() {
            box.removeAllViews()
            val list = p.bookmarks.sortedBy { it.line }
            if (list.isEmpty()) {
                val t = mkTv("No bookmarks yet.\nCtrl+B, or tap the left gutter, to add.", 0xFF999999.toInt(), 13f)
                t.setPadding(dp(12), dp(12), dp(12), dp(12))
                box.addView(t)
            }
            for (b in list) {
                val row = LinearLayout(this)
                row.orientation = LinearLayout.HORIZONTAL
                row.gravity = Gravity.CENTER_VERTICAL
                val ln = mkTv("L${b.line + 1}", cWhite, 12f)
                ln.setBackgroundColor(0xFF27AE60.toInt())
                ln.setPadding(dp(6), dp(2), dp(6), dp(2))
                row.addView(ln)
                val nameBtn = mkBtn(b.name, 0xFF1E2E1E.toInt(), 0xFF7FFFB2.toInt()) {
                    p.view.setCaret(b.line, 0, false)
                    p.view.scrollToLine(b.line, true)
                    dref[0]?.dismiss()
                }
                nameBtn.gravity = Gravity.START or Gravity.CENTER_VERTICAL
                row.addView(nameBtn, lp(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f, 2))
                row.addView(mkBtn("✎", 0xFF3C3C3C.toInt(), cWhite) {
                    inputDialog("Rename bookmark", b.name) { nm -> if (nm.isNotBlank()) { b.name = nm.trim(); sessionDirty = true; fill() } }
                }, lp(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, 0f, 2))
                row.addView(mkBtn("✖", 0xFF5C1A1A.toInt(), 0xFFFFAAAA.toInt()) {
                    p.bookmarks.remove(b); p.rebuildBm(); sessionDirty = true; fill()
                }, lp(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, 0f, 2))
                box.addView(row)
            }
        }
        fill()
        val dlg = DBuilder(this).setTitle("🔵 Bookmarks  (F2 next · Shift+F2 prev)").setView(sv)
            .setPositiveButton("Close", null)
            .setNeutralButton("Add here") { _, _ ->
                if (p.bookmarks.none { it.line == p.view.caretL }) toggleBookmarkAt(p, p.view.caretL)
            }
            .setNegativeButton("Clear all") { _, _ ->
                p.bookmarks.clear(); p.rebuildBm(); sessionDirty = true; toast("All bookmarks cleared")
            }.create()
        dref[0] = dlg
        dlg.show()
    }

    // ───────── find / replace / mark ─────────
    private fun buildPattern(): Pattern? {
        var s = findEt.text.toString()
        if (s.isEmpty()) { setFindStatus("⚠ Enter text to find", 0xFFE74C3C.toInt()); return null }
        try {
            if (!cbRegex.isChecked) s = Pattern.quote(s)
            if (cbWhole.isChecked) s = "\\b" + s + "\\b"
            var flags = 0
            if (!cbCase.isChecked) flags = Pattern.CASE_INSENSITIVE or Pattern.UNICODE_CASE
            return Pattern.compile(s, flags)
        } catch (e: Exception) {
            setFindStatus("⚠ Invalid pattern: " + (e.message ?: "").lines().firstOrNull(), 0xFFE74C3C.toInt())
            return null
        }
    }

    fun doFind(forward: Boolean) {
        val p = cur ?: return
        val pat = buildPattern() ?: return
        if (searching) { toast("A search is already running"); return }
        val d = p.doc
        val v = p.view
        var sl = v.caretL
        var sc = v.caretC
        if (v.hasSel) {
            val a = v.selNorm()
            if (forward) { sl = a[2]; sc = a[3] } else { sl = a[0]; sc = a[1] }
        }
        val l0 = sl
        val c0 = sc
        searching = true
        searchCancel = false
        setFindStatus("⏳ Searching…", 0xFFE67E22.toInt())
        Thread {
            var hit: IntArray? = null
            try {
                hit = d.search(pat, l0, c0, forward, { searchCancel }, { n -> ui.post { if (searching) setFindStatus("⏳ Searching… line $n", 0xFFE67E22.toInt()) } })
            } catch (e: Exception) { }
            val h = hit
            ui.post {
                searching = false
                if (p.doc === d) {
                    if (h == null) {
                        setFindStatus(if (searchCancel) "■ Search stopped" else "No matches found.", 0xFFE74C3C.toInt())
                    } else {
                        v.foundL = h[0]; v.foundC1 = h[1]; v.foundC2 = h[2]
                        if (forward) v.setCaret(h[0], h[2], false) else v.setCaret(h[0], h[1], false)
                        v.scrollToLine(h[0], false)
                        v.ensureCaretVisible()
                        setFindStatus("✔ Found at Ln ${h[0] + 1}, Col ${h[1] + 1}", 0xFF2ECC71.toInt())
                    }
                }
            }
        }.start()
    }

    private fun replaceOne() {
        val p = cur ?: return
        val v = p.view
        val pat = buildPattern() ?: return
        if (p.doc.indexing) { toast("Still indexing — editing unlocks when done"); return }
        val rtxt = replEt.text.toString()
        if (v.foundL >= 0 && v.foundL < p.doc.total) {
            val l = v.foundL
            val t = p.doc.getLine(l)
            val a = minOf(v.foundC1, t.length)
            val b = minOf(v.foundC2, t.length)
            val sb = StringBuilder()
            val m = pat.matcher(t)
            if (cbRegex.isChecked && m.find(a) && m.start() == a) Repl(rtxt, true).expand(m, sb) else sb.append(rtxt)
            val nt = t.substring(0, a) + sb.toString() + t.substring(b)
            p.doc.edit(l, l + 1, arrayOf(nt), v.caretL, v.caretC, null)
            v.caretL = l; v.caretC = a + sb.length; v.ancL = l; v.ancC = v.caretC
            v.afterEdit()
        } else if (v.hasSel) {
            v.insertText(rtxt, null)
        }
        doFind(true)
    }

    private fun approxSize(d: Doc): Long {
        var inl = 0L
        var orig = false
        for (pc in d.st.pieces) {
            val il = pc.lines
            if (il == null) orig = true else for (s in il) inl += s.length.toLong() + 1L
        }
        return inl + (if (orig) (d.src?.size ?: 0L) else 0L)
    }

    private fun cleanWork() {
        try {
            val keep = HashSet<String>()
            for (p in panes) if (p.doc.srcKind == "file") keep.add(File(p.doc.srcRef).absolutePath)
            val fs = workDir().listFiles() ?: arrayOf<File>()
            for (f in fs) if (!keep.contains(f.absolutePath)) f.delete()
        } catch (e: Exception) { }
    }

    private fun workDir(): File {
        val f = File(filesDir, "work")
        if (!f.exists()) f.mkdirs()
        return f
    }

    private fun computeReplace(d: Doc, pat: Pattern, repl: Repl): ReplaceResult {
        val res = ReplaceResult(0, null, null)
        val tot = d.total
        val cnt = IntArray(1)
        val m = pat.matcher("")
        if (approxSize(d) <= 8L * 1024L * 1024L) {
            val sb = StringBuilder()
            for (l in 0 until tot) {
                if (l > 0) sb.append('\n')
                sb.append(d.getLine(l))
            }
            val out = repl.applyLine(m, sb.toString(), cnt)
            if (out != null) res.newLines = out.split("\n").toTypedArray()
        } else {
            val f = File(workDir(), "work_" + System.nanoTime() + ".txt")
            val w = BufferedWriter(OutputStreamWriter(FileOutputStream(f), Charsets.UTF_8), 1 shl 16)
            val eolS = d.eol
            var l = 0
            while (l < tot) {
                val t = d.getLine(l)
                val r = repl.applyLine(m, t, cnt)
                w.write(r ?: t)
                if (l < tot - 1) w.write(eolS)
                l++
                if ((l and 0xFFFF) == 0) {
                    if (opCancel) break
                    busyUpdate("Replacing… " + (l.toLong() * 100L / tot) + "%  (" + cnt[0] + " found)")
                }
            }
            w.close()
            if (cnt[0] == 0 || opCancel) { f.delete() } else res.workFile = f
        }
        res.count = if (opCancel) 0 else cnt[0]
        return res
    }

    private fun swapToWorkFile(p: Pane, f: File) {
        val s = openFileSrc(f)
        val old = p.doc
        val nd = Doc()
        nd.src = s; nd.srcKind = "file"; nd.srcRef = f.absolutePath
        nd.target = old.target; nd.eol = old.eol; nd.modified = true
        val v = p.view
        val cl = v.caretL; val cc = v.caretC; val top = v.topLine
        p.swapIn(nd)
        nd.afterIndex = {
            if (p.doc === nd) {
                v.setCaret(cl, cc, false)
                v.topLine = top
                v.clearOverlays()
                p.onTextChanged()
                v.invalidate()
            }
        }
        nd.beginIndex(ui, cacheDir, 0L)
        v.clearOverlays()
        p.onTextChanged()
        v.invalidate()
    }

    fun swapDoc(p: Pane, back: Boolean) {
        val v = p.view
        val cl = v.caretL; val cc = v.caretC; val top = v.topLine
        val ok = if (back) p.undoSwap() else p.redoSwap()
        if (!ok) return
        v.clearOverlays()
        v.setCaret(cl, cc, false)
        v.topLine = minOf(top, maxOf(0, p.doc.total - 1))
        v.topPx = 0f
        p.onTextChanged()
        updateStatus()
        v.invalidate()
        toast(if (back) "↩ Undid Replace All" else "↪ Redid Replace All")
    }

    private fun applyReplace(p: Pane, r: ReplaceResult) {
        if (r.count == 0) return
        val v = p.view
        val nl = r.newLines
        val wf = r.workFile
        if (nl != null) {
            p.doc.edit(0, p.doc.total, nl, v.caretL, v.caretC, null)
            v.afterEdit()
        } else if (wf != null) {
            swapToWorkFile(p, wf)
        }
    }

    private fun replaceAll() {
        val pat = buildPattern() ?: return
        val repl = Repl(replEt.text.toString(), cbRegex.isChecked)
        val targets = ArrayList<Pane>()
        if (rbAll.isChecked) targets.addAll(panes) else { val c = cur ?: return; targets.add(c) }
        for (t in targets) if (t.doc.indexing) { toast("A file is still indexing — try again shortly"); return }
        DBuilder(this).setTitle("Replace All")
            .setMessage("Replace all matches in ${targets.size} tab(s)?\nVery large files (>8 MB) are rewritten through a temporary copy (needs free space about the file size). Undo works for the last 3 such replaces while the app stays open.")
            .setPositiveButton("Replace All") { _, _ ->
                val results = HashMap<Pane, ReplaceResult>()
                runTask("Replacing…", {
                    for (t in targets) {
                        if (opCancel) break
                        results[t] = computeReplace(t.doc, pat, repl)
                    }
                }, { err ->
                    if (err != null) toast("❌ $err") else {
                        var total = 0
                        for (t in targets) {
                            val r = results[t] ?: continue
                            total += r.count
                            applyReplace(t, r)
                        }
                        setFindStatus("✔ Replaced $total occurrence(s) in ${targets.size} tab(s)", 0xFF2ECC71.toInt())
                    }
                })
            }.setNegativeButton("Cancel", null).show()
    }

    private fun markAll() {
        val p = cur ?: return
        val pat = buildPattern() ?: return
        val d = p.doc
        val colour = markColour
        val found = HashMap<Int, ArrayList<IntArray>>()
        val lines = ArrayList<Int>()
        var total = 0
        runTask("Marking all matches…", {
            val m = pat.matcher("")
            val tot = d.total
            var l = 0
            while (l < tot && total < 200000) {
                val t = d.getLine(l)
                m.reset(t)
                var pos = 0
                var list: ArrayList<IntArray>? = null
                while (pos <= t.length && m.find(pos)) {
                    if (m.end() > m.start()) {
                        if (list == null) list = ArrayList()
                        list.add(intArrayOf(m.start(), m.end(), colour))
                        total++
                        pos = m.end()
                    } else pos = m.end() + 1
                }
                if (list != null) { found[l] = list; lines.add(l) }
                l++
                if ((l and 0xFFFF) == 0) {
                    if (opCancel) break
                    busyUpdate("Marking… " + (l.toLong() * 100L / tot) + "%  (" + total + " found)")
                }
            }
        }, { err ->
            if (err != null) toast("❌ $err")
            else if (total == 0) setFindStatus("No matches found.", 0xFFE74C3C.toInt())
            else {
                val v = p.view
                v.marks.clear()
                v.marks.putAll(found)
                var added = 0
                if (cbAlsoBm.isChecked) {
                    val term = findEt.text.toString()
                    for (l in lines) {
                        if (added >= 20000) break
                        if (p.bmLines.contains(l)) continue
                        p.bookmarks.add(Bm(l, "[" + term + "] " + p.doc.getLine(l).trim().take(30)))
                        p.bmLines.add(l)
                        added++
                    }
                    p.rebuildBm()
                }
                v.scrollToLine(lines[0], false)
                v.invalidate()
                sessionDirty = true
                setFindStatus("✦ Marked $total match(es) on ${lines.size} line(s)" + (if (total >= 200000) " (capped)" else ""), 0xFF2ECC71.toInt())
            }
        })
    }

    private fun clearMarks() {
        for (p in panes) { p.view.marks.clear(); p.view.foundL = -1; p.view.invalidate() }
        setFindStatus("Marks cleared.", 0xFF7F8C8D.toInt())
    }

    // ───────── Special Copy Mode ─────────
    fun toggleScm() {
        scmActive = !scmActive
        scmStart = -1
        scmEnd = -1
        for (p in panes) { p.view.scmHl = null; p.view.scmStartLine = -1; p.view.invalidate() }
        if (scmActive) {
            scmToggleBtn.text = "📌 Special Copy Mode: ON"
            scmToggleBtn.background = roundBg(0xFF8E44AD.toInt(), 5)
            scmStatusTv.text = "Tap the START line (text or line number), then the END line, then S / Save"
            scmStatusTv.setTextColor(0xFFD7BDE2.toInt())
            if (panelWhich != 2) showPanel(2)
        } else {
            scmToggleBtn.text = "📌 Special Copy Mode: OFF"
            scmToggleBtn.background = roundBg(0xFF4A235A.toInt(), 5)
            scmStatusTv.text = "Enable mode → tap START line → tap END line → press S (or Save)"
            scmStatusTv.setTextColor(0xFF7F8C8D.toInt())
        }
    }

    private fun scmChooseFile() {
        DBuilder(this).setTitle("Special Copy output file")
            .setItems(arrayOf("Create a new file…", "Append to an existing file…")) { _, which ->
                if (which == 0) {
                    val i = Intent(Intent.ACTION_CREATE_DOCUMENT)
                    i.addCategory(Intent.CATEGORY_OPENABLE)
                    i.type = "text/plain"
                    i.putExtra(Intent.EXTRA_TITLE, "special_copy.txt")
                    startActivityForResult(i, RC_SCMFILE)
                } else {
                    val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
                    i.addCategory(Intent.CATEGORY_OPENABLE)
                    i.type = "*/*"
                    i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
                    startActivityForResult(i, RC_SCMFILE)
                }
            }.show()
    }

    private fun scmClearFile() {
        scmUri = null
        scmFileTv.text = "No file chosen"
        scmFileTv.setTextColor(0xFF7F8C8D.toInt())
        sessionDirty = true
    }

    private fun scmSelectManual() {
        val p = cur ?: return
        val f = scmFromEt.text.toString().trim().toIntOrNull()
        val t0 = scmToEt.text.toString().trim().toIntOrNull()
        if (f == null) { toast("Enter the FROM line number"); return }
        val t = t0 ?: f
        val tot = p.doc.total
        val a = minOf(f, t)
        val b = maxOf(f, t)
        if (a < 1 || b > tot) { toast("Lines must be within 1 – $tot"); return }
        if (!scmActive) toggleScm()
        scmPane = p
        val v = p.view
        for (q in panes) { q.view.scmHl = null; q.view.scmStartLine = -1; q.view.invalidate() }
        scmStart = a - 1
        if (a == b) {
            scmEnd = -1
            v.scmStartLine = a - 1
            scmStatusTv.text = "✅ Line $a selected — press S / Save"
        } else {
            scmEnd = b - 1
            v.scmHl = intArrayOf(a - 1, b - 1)
            scmStatusTv.text = "✅ Range L$a–L$b (${b - a + 1} lines) — press S / Save. R = clear"
        }
        scmStatusTv.setTextColor(0xFF2ECC71.toInt())
        scmFromEt.setText(a.toString())
        scmToEt.setText(b.toString())
        v.scrollToLine(a - 1, false)
        v.invalidate()
    }

    private fun scmOnClick(p: Pane, line: Int) {
        val v = p.view
        if (scmStart < 0) {
            scmStart = line
            scmEnd = -1
            v.scmHl = null
            v.scmStartLine = line
            scmFromEt.setText((line + 1).toString())
            scmToEt.setText("")
            scmStatusTv.text = "📍 START = L${line + 1}. Tap END line for a range, or press S to save just this line"
            scmStatusTv.setTextColor(0xFFF39C12.toInt())
        } else {
            val s = minOf(scmStart, line)
            val e = maxOf(scmStart, line)
            scmStart = s
            scmEnd = e
            v.scmStartLine = -1
            v.scmHl = intArrayOf(s, e)
            scmFromEt.setText((s + 1).toString())
            scmToEt.setText((e + 1).toString())
            scmStatusTv.text = "✅ Range L${s + 1}–L${e + 1} (${e - s + 1} lines) — press S / Save. R = clear"
            scmStatusTv.setTextColor(0xFF2ECC71.toInt())
        }
        v.invalidate()
    }

    fun scmClearSel() {
        scmStart = -1
        scmEnd = -1
        for (p in panes) { p.view.scmHl = null; p.view.scmStartLine = -1; p.view.invalidate() }
        scmFromEt.setText("")
        scmToEt.setText("")
        scmClearFile()
        scmStatusTv.text = "Selection and output file cleared. Tap a START line; you will be asked for an output file when you save."
        scmStatusTv.setTextColor(0xFF7F8C8D.toInt())
    }

    fun scmSave() {
        val p = scmPane ?: cur ?: return
        if (scmStart < 0) { toast("Tap a START line first"); return }
        val uri = scmUri
        if (uri == null) { pendingScmSave = true; scmChooseFile(); return }
        val s = scmStart
        val e = if (scmEnd >= 0) scmEnd else scmStart
        val d = p.doc
        runTask("Saving lines ${s + 1}–${e + 1}…", {
            val os = contentResolver.openOutputStream(uri, "wa") ?: throw IOException("Cannot open output file")
            val bo = BufferedOutputStream(os, 1 shl 16)
            var l = s
            while (l <= e) {
                bo.write(d.getLine(l).toByteArray(Charsets.UTF_8))
                if (l < e) bo.write(10)
                l++
                if ((l and 0xFFFF) == 0) {
                    if (opCancel) break
                    busyUpdate("Saving… " + ((l - s).toLong() * 100L / (e - s + 1)) + "%")
                }
            }
            bo.write(byteArrayOf(10, 10, 10))
            bo.flush()
            bo.close()
        }, { err ->
            if (err != null) {
                scmStatusTv.text = "❌ $err"
                scmStatusTv.setTextColor(0xFFE74C3C.toInt())
            } else {
                scmStatusTv.text = "💾 Saved L${s + 1}–L${e + 1} → " + queryName(uri) + " | tap a new START line"
                scmStatusTv.setTextColor(0xFF2ECC71.toInt())
                scmStart = -1; scmEnd = -1
                for (q in panes) { q.view.scmHl = null; q.view.scmStartLine = -1; q.view.invalidate() }
            }
        })
    }

    // ───────── Delete Lines panel ─────────
    fun openDelPanel() {
        val p = cur ?: return
        if (panelWhich == 3) { showPanel(0); return }
        delPane = p
        delPickStep = 0
        delPickRowObj = null
        delRows.clear()
        delPairsBox.removeAllViews()
        delSummary.text = ""
        addDelRow()
        showPanel(3)
    }

    private fun addDelRow() {
        val frame = LinearLayout(this)
        frame.orientation = LinearLayout.VERTICAL
        frame.setBackgroundColor(0xFFD6EAF8.toInt())
        frame.setPadding(dp(4), dp(4), dp(4), dp(4))
        val fp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        fp.setMargins(0, dp(3), 0, dp(3))
        frame.layoutParams = fp
        val l1 = flowRow()
        val sl = mkTv("START: —", 0xFF1A5276.toInt(), 12f)
        val el = mkTv("   END: —", 0xFF1A5276.toInt(), 12f)
        addGap(l1, mkTv("Pair ${delRows.size + 1}  ", 0xFF1A252F.toInt(), 12f))
        addGap(l1, sl)
        addGap(l1, el)
        frame.addView(l1)
        val l2 = flowRow()
        val se = mkEt("start", true, 70)
        val ee = mkEt("end", true, 70)
        addGap(l2, se, 70)
        addGap(l2, mkTv("→", 0xFF1A252F.toInt(), 12f))
        addGap(l2, ee, 70)
        val pick = mkBtn("👆 Pick", 0xFF8E44AD.toInt(), cWhite) { }
        val row = DelRow(frame, sl, el, se, ee, pick)
        pick.setOnClickListener {
            delPickRowObj = row
            delPickStep = 1
            delInstr.text = "👆 Tap the START line in the editor (text or line number)"
        }
        addGap(l2, pick)
        addGap(l2, mkBtn("✔ Apply", 0xFF27AE60.toInt(), cWhite) { applyManual(row) })
        addGap(l2, mkBtn("✖", 0xFFC0392B.toInt(), cWhite) {
            row.active = false
            delPairsBox.removeView(frame)
            delRows.remove(row)
        })
        frame.addView(l2)
        delRows.add(row)
        delPairsBox.addView(frame)
    }

    private fun delStoreLine(n: Int) {
        val row = delPickRowObj ?: return
        if (delPickStep == 1) {
            row.s = n
            row.startEt.setText(n.toString())
            row.startLbl.text = "START: $n"
            delPickStep = 2
            delInstr.text = "👆 Now tap the END line"
        } else if (delPickStep == 2) {
            row.e = n
            row.endEt.setText(n.toString())
            row.endLbl.text = "   END: $n"
            delPickStep = 0
            delInstr.text = "✔ Range set. Add another pair, Preview, or DELETE ALL."
        }
    }

    private fun applyManual(row: DelRow) {
        val s = row.startEt.text.toString().trim().toIntOrNull()
        val e = row.endEt.text.toString().trim().toIntOrNull()
        if (s == null || e == null) { toast("Enter both numbers"); return }
        row.s = s; row.e = e
        row.startLbl.text = "START: $s"
        row.endLbl.text = "   END: $e"
    }

    private fun collectPairs(): ArrayList<IntArray> {
        val out = ArrayList<IntArray>()
        for (r in delRows) {
            val s = r.startEt.text.toString().trim().toIntOrNull() ?: (if (r.s > 0) r.s else null)
            val e = r.endEt.text.toString().trim().toIntOrNull() ?: (if (r.e > 0) r.e else null)
            if (s != null && e != null) out.add(intArrayOf(minOf(s, e), maxOf(s, e)))
        }
        return out
    }

    private fun parsePasted(): Parsed {
        val pairs = ArrayList<IntArray>()
        val bad = ArrayList<Int>()
        val re = Regex("^\\s*(\\d+)\\s*[-,;:\\s]+\\s*(\\d+)\\s*$")
        var i = 0
        for (ln in delPasteEt.text.toString().split("\n")) {
            i++
            if (ln.isBlank()) continue
            val m = re.find(ln)
            if (m == null) { bad.add(i); continue }
            val a = m.groupValues[1].toIntOrNull()
            val b = m.groupValues[2].toIntOrNull()
            if (a == null || b == null) { bad.add(i); continue }
            pairs.add(intArrayOf(minOf(a, b), maxOf(a, b)))
        }
        return Parsed(pairs, bad)
    }

    private fun previewPairs(pairs: ArrayList<IntArray>) {
        val p = delPane ?: cur ?: return
        val tot = p.doc.total
        val rs = ArrayList<IntArray>()
        var lines = 0
        for (q in pairs) {
            if (q[0] > tot) continue
            val e = minOf(q[1], tot)
            rs.add(intArrayOf(q[0] - 1, e - 1))
            lines += e - q[0] + 1
        }
        if (rs.isEmpty()) { delSummary.text = "⚠ No valid ranges (document has $tot lines)"; return }
        p.view.delPreview = rs
        p.view.scrollToLine(rs[0][0], false)
        p.view.invalidate()
        delSummary.text = "👁 ${rs.size} range(s), $lines line(s) highlighted in red"
    }

    private fun previewFromPaste() {
        val ps = parsePasted()
        if (ps.pairs.isEmpty()) { delSummary.text = "⚠ No valid pairs found"; return }
        previewPairs(ps.pairs)
        if (ps.bad.isNotEmpty()) delSummary.text = delSummary.text.toString() + "  (ignored text lines: " + ps.bad.joinToString(",") + ")"
    }

    private fun previewAllPairs() {
        val pr = collectPairs()
        if (pr.isEmpty()) { delSummary.text = "⚠ Add at least one pair"; return }
        previewPairs(pr)
    }

    private fun deleteFromPaste() {
        val ps = parsePasted()
        if (ps.pairs.isEmpty()) { delSummary.text = "⚠ No valid pairs found"; return }
        doDelete(ps.pairs)
    }

    private fun deleteAllPairs() {
        val pr = collectPairs()
        if (pr.isEmpty()) { delSummary.text = "⚠ Add at least one pair"; return }
        doDelete(pr)
    }

    private fun doDelete(pairs: ArrayList<IntArray>) {
        val p = delPane ?: cur ?: return
        if (p.doc.indexing) { toast("Still indexing — try again in a moment"); return }
        val tot = p.doc.total
        val rs = ArrayList<IntArray>()
        var lines = 0L
        for (q in pairs) {
            if (q[0] > tot) continue
            val e = minOf(q[1], tot)
            rs.add(intArrayOf(q[0] - 1, e - 1))
            lines += (e - q[0] + 1).toLong()
        }
        if (rs.isEmpty()) { delSummary.text = "⚠ No valid ranges (document has $tot lines)"; return }
        DBuilder(this).setTitle("Delete lines")
            .setMessage("Delete up to $lines line(s) in ${rs.size} range(s)?  (Undo available)")
            .setPositiveButton("Delete") { _, _ ->
                val v = p.view
                p.doc.deleteRanges(rs, v.caretL, v.caretC)
                v.delPreview = null
                v.clampCaret()
                v.afterEdit()
                delSummary.text = "✔ Deleted ${rs.size} range(s)"
            }.setNegativeButton("Cancel", null).show()
    }

    // ───────── Remove blank line between A and B ─────────
    private fun scanBlank(d: Doc, a: String, b: String, ranges: ArrayList<IntArray>?): Int {
        var count = 0
        val tot = d.total
        var i = 0
        while (i < tot) {
            if (d.getLine(i) == a) {
                var j = i + 1
                var blanks = 0
                while (j < tot && d.getLine(j).isBlank()) { blanks++; j++ }
                if (j < tot && d.getLine(j) == b && blanks > 0) {
                    ranges?.add(intArrayOf(i + 1, j - 1))
                    count += blanks
                    i = j
                    continue
                }
            }
            i++
            if ((i and 0xFFFFF) == 0) {
                if (opCancel) break
                busyUpdate("Scanning… " + (i.toLong() * 100L / tot) + "%")
            }
        }
        return count
    }

    fun removeBlankDialog() {
        if (cur == null) return
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        box.setPadding(dp(14), dp(8), dp(14), dp(4))
        box.addView(mkTv("Line A (exact text of the line ABOVE the blank lines):", cTxt, 12f))
        val ea = EditText(this); ea.setSingleLine(true); ea.setTextColor(cWhite)
        box.addView(ea)
        box.addView(mkTv("Line B (exact text of the line BELOW the blank lines):", cTxt, 12f))
        val eb = EditText(this); eb.setSingleLine(true); eb.setTextColor(cWhite)
        box.addView(eb)
        val rg = RadioGroup(this)
        rg.orientation = RadioGroup.HORIZONTAL
        val r1 = RadioButton(this); r1.text = "Current Tab"; r1.id = View.generateViewId()
        val r2 = RadioButton(this); r2.text = "All Opened Tabs"; r2.id = View.generateViewId()
        r1.setTextColor(cTxt); r2.setTextColor(cTxt)
        rg.addView(r1); rg.addView(r2); rg.check(r1.id)
        box.addView(rg)
        val st = mkTv("", 0xFFF39C12.toInt(), 12f)
        box.addView(st)
        val dlg = DBuilder(this).setTitle("🔗 Remove blank lines between A and B").setView(box)
            .setPositiveButton("Count", null).setNeutralButton("Apply", null).setNegativeButton("Close", null).create()
        dlg.show()
        fun targets(): ArrayList<Pane> {
            val t = ArrayList<Pane>()
            if (r2.isChecked) t.addAll(panes) else { val c = cur; if (c != null) t.add(c) }
            return t
        }
        dlg.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener {
            val a = ea.text.toString(); val b = eb.text.toString()
            if (a.isEmpty() || b.isEmpty()) { st.text = "⚠ Enter both lines"; return@setOnClickListener }
            val tg = targets()
            var total = 0
            runTask("Counting…", { for (p in tg) { if (opCancel) break; total += scanBlank(p.doc, a, b, null) } },
                { err -> st.text = if (err != null) "❌ $err" else "🔍 $total blank line(s) would be removed" })
        }
        dlg.getButton(AlertDialog.BUTTON_NEUTRAL).setOnClickListener {
            val a = ea.text.toString(); val b = eb.text.toString()
            if (a.isEmpty() || b.isEmpty()) { st.text = "⚠ Enter both lines"; return@setOnClickListener }
            val tg = targets()
            for (p in tg) if (p.doc.indexing) { st.text = "⚠ A file is still indexing"; return@setOnClickListener }
            val res = HashMap<Pane, ArrayList<IntArray>>()
            var total = 0
            runTask("Removing…", {
                for (p in tg) {
                    if (opCancel) break
                    val rs = ArrayList<IntArray>()
                    total += scanBlank(p.doc, a, b, rs)
                    res[p] = rs
                }
            }, { err ->
                if (err != null) st.text = "❌ $err" else {
                    for (p in tg) {
                        val rs = res[p] ?: continue
                        if (rs.isEmpty()) continue
                        p.doc.deleteRanges(rs, p.view.caretL, p.view.caretC)
                        p.view.clampCaret()
                        p.view.afterEdit()
                    }
                    st.text = "✔ Removed $total blank line(s)"
                }
            })
        }
    }

    // ───────── format dialogs / menu ─────────
    private fun fontDialog() {
        val p = cur ?: return
        val v = p.view
        val fams = arrayOf("monospace", "sans-serif", "serif", "sans-serif-condensed", "casual", "cursive")
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        box.setPadding(dp(14), dp(8), dp(14), dp(4))
        val rg = RadioGroup(this)
        val ids = IntArray(fams.size)
        for (i in fams.indices) {
            val rb = RadioButton(this)
            rb.text = fams[i]; rb.id = View.generateViewId(); rb.setTextColor(cTxt)
            ids[i] = rb.id
            rg.addView(rb)
            if (fams[i] == v.fontFamily) rg.check(rb.id)
        }
        box.addView(rg)
        val sz = EditText(this)
        sz.inputType = InputType.TYPE_CLASS_NUMBER
        sz.setText(v.fontSize.toString())
        sz.setTextColor(cWhite)
        box.addView(mkTv("Size:", cTxt, 12f))
        box.addView(sz)
        val cb = CheckBox(this); cb.text = "Bold"; cb.isChecked = v.bold; cb.setTextColor(cTxt)
        val ci = CheckBox(this); ci.text = "Italic"; ci.isChecked = v.italic; ci.setTextColor(cTxt)
        box.addView(cb); box.addView(ci)
        val sv = ScrollView(this)
        sv.addView(box)
        DBuilder(this).setTitle("Font").setView(sv)
            .setPositiveButton("Apply") { _, _ ->
                for (i in fams.indices) if (rg.checkedRadioButtonId == ids[i]) v.fontFamily = fams[i]
                v.fontSize = (sz.text.toString().toIntOrNull() ?: v.fontSize).coerceIn(6, 72)
                v.bold = cb.isChecked
                v.italic = ci.isChecked
                v.applyFont()
                sessionDirty = true
            }.setNegativeButton("Cancel", null).show()
    }

    private fun colourDialog(title: String, init: Int, ok: (Int) -> Unit) {
        val pal = intArrayOf(
            0xFFFFFFFF.toInt(), 0xFFD4D4D4.toInt(), 0xFF9CDCFE.toInt(), 0xFF4EC9B0.toInt(), 0xFFCE9178.toInt(), 0xFFDCDCAA.toInt(),
            0xFFC586C0.toInt(), 0xFF6A9955.toInt(), 0xFFF1C40F.toInt(), 0xFFE74C3C.toInt(), 0xFF2ECC71.toInt(), 0xFF3498DB.toInt(),
            0xFF000000.toInt(), 0xFF1E1E1E.toInt(), 0xFF252526.toInt(), 0xFF0D1117.toInt(), 0xFF002B36.toInt(), 0xFF1A1A2E.toInt(),
            0xFF2D2D2D.toInt(), 0xFF3C3C3C.toInt(), 0xFFFFF8DC.toInt(), 0xFFF5F5F5.toInt(), 0xFFFDF6E3.toInt(), 0xFFE8E8E8.toInt())
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        box.setPadding(dp(14), dp(8), dp(14), dp(4))
        val hex = EditText(this)
        hex.setSingleLine(true)
        hex.setTextColor(cWhite)
        hex.setText(String.format("#%06X", init and 0xFFFFFF))
        var rowL: LinearLayout? = null
        for (i in pal.indices) {
            if (i % 6 == 0) { rowL = LinearLayout(this); rowL.orientation = LinearLayout.HORIZONTAL; box.addView(rowL) }
            val c = pal[i]
            val b = mkBtn("", c, cWhite) { hex.setText(String.format("#%06X", c and 0xFFFFFF)) }
            rowL?.addView(b, lp(0, dp(36), 1f, 2))
        }
        box.addView(mkTv("Hex colour:", cTxt, 12f))
        box.addView(hex)
        DBuilder(this).setTitle(title).setView(box)
            .setPositiveButton("OK") { _, _ ->
                try { ok(android.graphics.Color.parseColor(hex.text.toString().trim())) } catch (e: Exception) { toast("Invalid colour") }
            }.setNegativeButton("Cancel", null).show()
    }

    private fun showMenu() {
        val p = cur ?: return
        val items = arrayOf(
            "Open in New Tab…", "Save As…", "Go to Line… (Ctrl+G)", "Special Copy Mode (Ctrl+M)",
            "Toggle Bookmark (Ctrl+B)", "Next Bookmark (F2)", "Previous Bookmark (Shift+F2)", "Clear All Bookmarks",
            "Font…", "Text Colour…", "Background Colour…", "Zoom In (Ctrl++)", "Zoom Out (Ctrl+-)", "Reset Zoom",
            "Next Tab (Ctrl+Tab)", "Previous Tab (Ctrl+Shift+Tab)", "Keyboard on/off", "Show / Hide Line Numbers", "About", "📌 Floating window (Ctrl+Shift+T)", "Exit")
        DBuilder(this).setTitle("Menu").setItems(items) { _, which ->
            when (which) {
                0 -> openFiles(true)
                1 -> saveAs(p, null)
                2 -> focusGoto()
                3 -> toggleScm()
                4 -> toggleBookmarkAt(p, p.view.caretL)
                5 -> bmNext(true)
                6 -> bmNext(false)
                7 -> { p.bookmarks.clear(); p.rebuildBm(); sessionDirty = true }
                8 -> fontDialog()
                9 -> colourDialog("Text colour", p.view.fg) { c -> p.view.fg = c; p.view.invalidate(); sessionDirty = true }
                10 -> colourDialog("Background colour", p.view.bgc) { c -> p.view.bgc = c; p.view.invalidate(); sessionDirty = true }
                11 -> zoomBy(1)
                12 -> zoomBy(-1)
                13 -> { p.view.fontSize = 11; p.view.applyFont(); sessionDirty = true }
                14 -> nextTab(1)
                15 -> nextTab(-1)
                16 -> {
                    val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
                    if (imm.isActive(p.view)) imm.hideSoftInputFromWindow(p.view.windowToken, 0) else { p.view.requestFocus(); p.view.showKeyboard() }
                }
                17 -> toggleNums()
                18 -> showAbout()
                19 -> toggleFloat()
                20 -> { saveSessionNow(true); finish() }
                else -> { }
            }
        }.show()
    }

    private fun showAbout() {
        DBuilder(this).setTitle("Notepad — large-file edition").setMessage(
            "Opens text files of any size (bytes → many GB). Only the visible lines are ever loaded; the file is indexed in the background and you can start reading immediately. Editing unlocks when indexing finishes.\n\n" +
            "Shortcuts (external keyboard):\n" +
            " Ctrl+O / Ctrl+Shift+O  Open file(s)\n Ctrl+S / Ctrl+Shift+S  Save / Save As\n Ctrl+T  New tab · Ctrl+W  Close tab\n Ctrl+Tab / Ctrl+Shift+Tab  Switch tab\n" +
            " Ctrl+H / Ctrl+F  Find & Replace\n Ctrl+G  Go to line\n Ctrl+Z / Ctrl+Y  Undo / Redo\n Ctrl+B  Bookmark · F2 / Shift+F2  Next / previous\n Ctrl+Shift+B  Bookmark list\n" +
            " Ctrl+M  Special Copy Mode (then S = save range, R = clear)\n Ctrl+ + / Ctrl+ −  Zoom (also Ctrl+wheel, pinch)\n" +
            " Keys U / D  Auto-scroll direction\n Shift+wheel  Sideways scroll\n Ctrl+Shift+T  Floating always-on-top window (drag title bar to move, drag edges/corners to resize)\n\n" +
            "Touch: drag = scroll, long-press = select, double-tap = select word, drag the right/bottom bars to jump anywhere in huge files, tap the left gutter (dot or line number) to add / remove a bookmark circle, tap the blue status bar to copy the current line number.").setPositiveButton("OK", null).show()
    }

    // ───────── files: open / save ─────────
    fun persist(uri: Uri) {
        try {
            contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
        } catch (e: Exception) {
            try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (e2: Exception) { }
        }
    }

    fun openFiles(newTab: Boolean) {
        pendingNewTab = newTab
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "*/*"
        i.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        startActivityForResult(i, RC_OPEN)
    }

    @Suppress("DEPRECATION")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (overlayOn) {
            skipAutoDock = true
            ui.postDelayed({ if (overlayOn) moveTaskToBack(true) }, 200)
        }
        if (resultCode != RESULT_OK || data == null) { pendingScmSave = false; return }
        if (requestCode == RC_OPEN) {
            val uris = ArrayList<Uri>()
            val cd = data.clipData
            if (cd != null) { for (k in 0 until cd.itemCount) uris.add(cd.getItemAt(k).uri) }
            else { val u = data.data; if (u != null) uris.add(u) }
            if (uris.isEmpty()) return
            for (u in uris) persist(u)
            if (pendingNewTab) {
                for (u in uris) loadUri(newPane(), u)
            } else {
                val p = cur ?: newPane()
                confirmUnsaved(p) {
                    loadUri(p, uris[0])
                    for (k in 1 until uris.size) loadUri(newPane(), uris[k])
                }
            }
        } else if (requestCode == RC_SAVEAS) {
            val u = data.data ?: return
            persist(u)
            val p = pendingSavePane ?: return
            val th = pendingSaveThen
            pendingSavePane = null
            pendingSaveThen = null
            doSave(p, u, th)
        } else if (requestCode == RC_SCMFILE) {
            val u = data.data ?: return
            persist(u)
            scmUri = u
            scmFileTv.text = "📄 " + queryName(u)
            scmFileTv.setTextColor(0xFF27AE60.toInt())
            sessionDirty = true
            if (pendingScmSave) { pendingScmSave = false; scmSave() }
        }
    }

    fun queryName(uri: Uri): String {
        try {
            val c = contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)
            if (c != null) {
                c.use {
                    if (it.moveToFirst()) {
                        val i = it.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                        if (i >= 0) { val s = it.getString(i); if (s != null) return s }
                    }
                }
            }
        } catch (e: Exception) { }
        val s = uri.lastPathSegment ?: "file"
        return s.substring(s.lastIndexOf('/') + 1)
    }

    private fun queryLastMod(uri: Uri): Long {
        try {
            val c = contentResolver.query(uri, arrayOf(DocumentsContract.Document.COLUMN_LAST_MODIFIED), null, null, null)
            if (c != null) {
                c.use {
                    if (it.moveToFirst()) {
                        val i = it.getColumnIndex(DocumentsContract.Document.COLUMN_LAST_MODIFIED)
                        if (i >= 0) return it.getLong(i)
                    }
                }
            }
        } catch (e: Exception) { }
        return 0L
    }

    fun loadUri(p: Pane, uri: Uri) {
        try {
            val s = openUriSrc(this, uri)
            val d = Doc()
            d.src = s; d.srcKind = "uri"; d.srcRef = uri.toString(); d.target = uri
            p.stopScroll()
            p.clearKept()
            p.replaceDoc(d)
            p.fileName = queryName(uri)
            p.bookmarks.clear()
            p.rebuildBm()
            val v = p.view
            v.caretL = 0; v.caretC = 0; v.ancL = 0; v.ancC = 0
            v.topLine = 0; v.topPx = 0f; v.hx = 0f
            v.clearOverlays()
            d.beginIndex(ui, cacheDir, queryLastMod(uri))
            if (cur !== p) selectPane(p)
            refreshTabs()
            updateStatus()
            v.invalidate()
            sessionDirty = true
        } catch (e: Exception) {
            toast("❌ Cannot open file: " + (e.message ?: e.toString()))
        }
    }

    fun savePane(p: Pane, then: (() -> Unit)?) {
        val t = p.doc.target
        if (t == null) saveAs(p, then) else doSave(p, t, then)
    }

    fun saveAs(p: Pane, then: (() -> Unit)?) {
        if (p.doc.indexing) { toast("Still indexing — wait until it finishes"); return }
        pendingSavePane = p
        pendingSaveThen = then
        val i = Intent(Intent.ACTION_CREATE_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "text/plain"
        i.putExtra(Intent.EXTRA_TITLE, if (p.fileName.isEmpty()) "untitled.txt" else p.fileName)
        @Suppress("DEPRECATION")
        startActivityForResult(i, RC_SAVEAS)
    }

    private fun doSave(p: Pane, uri: Uri, then: (() -> Unit)?) {
        val d = p.doc
        if (d.indexing) { toast("Still indexing — wait until it finishes"); return }
        val sameFile = d.srcKind == "uri" && d.srcRef == uri.toString()
        val needTmp = sameFile && d.hasOrigPieces()
        runTask("Saving…", {
            if (!needTmp) {
                val os = contentResolver.openOutputStream(uri, "wt") ?: throw IOException("Cannot open output")
                d.writeAll(os) { n -> busyUpdate("Saving… " + fmtSize(n)) }
                os.close()
            } else {
                val tmp = File(workDir(), "save_" + System.nanoTime() + ".tmp")
                val fo = FileOutputStream(tmp)
                d.writeAll(fo) { n -> busyUpdate("Preparing… " + fmtSize(n)) }
                fo.close()
                val os = contentResolver.openOutputStream(uri, "wt") ?: throw IOException("Cannot open output")
                val fi = FileInputStream(tmp)
                val buf = ByteArray(1 shl 20)
                var done = 0L
                while (true) {
                    val n = fi.read(buf)
                    if (n <= 0) break
                    os.write(buf, 0, n)
                    done += n.toLong()
                    busyUpdate("Writing… " + fmtSize(done))
                }
                os.close()
                fi.close()
                tmp.delete()
            }
        }, { err ->
            if (err != null) toast("❌ Save failed: $err")
            else {
                d.modified = false
                d.target = uri
                p.fileName = queryName(uri)
                p.dropKeptFor(uri.toString())
                if (sameFile) rebase(p, uri)
                refreshTabs()
                updateStatus()
                sessionDirty = true
                toast("💾 Saved")
                then?.invoke()
            }
        })
    }

    private fun rebase(p: Pane, uri: Uri) {
        try {
            val old = p.doc
            val s = openUriSrc(this, uri)
            val nd = Doc()
            nd.src = s; nd.srcKind = "uri"; nd.srcRef = uri.toString(); nd.target = uri
            nd.eol = old.eol
            val v = p.view
            val cl = v.caretL; val cc = v.caretC; val top = v.topLine
            p.clearKept()
            p.replaceDoc(nd)
            nd.afterIndex = {
                if (p.doc === nd) {
                    v.setCaret(cl, cc, false)
                    v.topLine = top
                    v.invalidate()
                    updateStatus()
                }
            }
            nd.beginIndex(ui, cacheDir, queryLastMod(uri))
        } catch (e: Exception) {
            toast("⚠ Saved, but could not re-open: " + (e.message ?: ""))
        }
    }

    // ───────── session ─────────
    private fun piecesJson(d: Doc): JSONArray? {
        if (d.pieceJson != null && d.pieceJsonVer == d.version) return d.pieceJson
        var chars = 0L
        val arr = JSONArray()
        for (pc in d.st.pieces) {
            val o = JSONObject()
            val il = pc.lines
            if (il == null) {
                o.put("t", "o"); o.put("s", pc.start); o.put("c", pc.count)
            } else {
                o.put("t", "i")
                val la = JSONArray()
                for (s in il) { la.put(s); chars += s.length.toLong() }
                if (chars > 6000000L) return null
                o.put("l", la)
            }
            arr.put(o)
        }
        d.pieceJson = arr
        d.pieceJsonVer = d.version
        return arr
    }

    private fun paneState(p: Pane): JSONObject {
        val o = JSONObject()
        val d = p.doc
        val v = p.view
        o.put("kind", d.srcKind)
        o.put("ref", d.srcRef)
        o.put("target", d.target?.toString() ?: "")
        o.put("name", p.fileName)
        o.put("size", d.src?.size ?: 0L)
        o.put("mod", d.modified)
        o.put("crlf", d.eol == "\r\n")
        if (d.modified || d.srcKind == "none") {
            val pj = piecesJson(d)
            if (pj != null) o.put("pieces", pj)
        }
        o.put("cl", v.caretL); o.put("cc", v.caretC)
        o.put("top", v.topLine)
        o.put("ff", v.fontFamily); o.put("fs", v.fontSize)
        o.put("bold", v.bold); o.put("ital", v.italic)
        o.put("fg", v.fg); o.put("bg", v.bgc); o.put("wrap", v.wrap); o.put("nums", v.showNums)
        o.put("speed", p.speed); o.put("dir", p.dir)
        val bms = JSONArray()
        for (b in p.bookmarks) { val bo = JSONObject(); bo.put("l", b.line); bo.put("n", b.name); bms.put(bo) }
        o.put("bms", bms)
        return o
    }

    fun saveSessionNow(sync: Boolean) {
        try {
            val o = JSONObject()
            val arr = JSONArray()
            for (p in panes) arr.put(paneState(p))
            o.put("tabs", arr)
            o.put("active", panes.indexOf(cur))
            o.put("scmUri", scmUri?.toString() ?: "")
            val s = o.toString()
            sessionDirty = false
            val work = Runnable {
                try {
                    val tmp = File(filesDir, "session.tmp")
                    tmp.writeText(s)
                    tmp.renameTo(File(filesDir, "session.json"))
                } catch (e: Exception) { }
            }
            if (sync) work.run() else Thread(work).start()
        } catch (e: Exception) { }
    }

    private fun restoreSession() {
        val f = File(filesDir, "session.json")
        if (!f.exists()) return
        try {
            val o = JSONObject(f.readText())
            val su = o.optString("scmUri", "")
            if (su.isNotEmpty()) {
                scmUri = Uri.parse(su)
                scmFileTv.text = "📄 " + queryName(scmUri!!)
                scmFileTv.setTextColor(0xFF27AE60.toInt())
            }
            val tabs = o.getJSONArray("tabs")
            for (i in 0 until tabs.length()) {
                val p = newPane()
                try { restorePane(p, tabs.getJSONObject(i)) } catch (e: Exception) { }
            }
            val a = o.optInt("active", 0)
            if (panes.isNotEmpty()) selectPane(panes[a.coerceIn(0, panes.size - 1)])
        } catch (e: Exception) { }
    }

    private fun restorePane(p: Pane, st: JSONObject) {
        val v = p.view
        v.fontFamily = st.optString("ff", "monospace")
        v.fontSize = st.optInt("fs", 11)
        v.bold = st.optBoolean("bold", false)
        v.italic = st.optBoolean("ital", false)
        v.fg = st.optInt("fg", v.fg)
        v.bgc = st.optInt("bg", v.bgc)
        v.wrap = st.optBoolean("wrap", false)
        v.showNums = st.optBoolean("nums", true)
        v.applyFont()
        p.speed = st.optDouble("speed", 3.0)
        p.dir = st.optString("dir", "down")
        val bms = st.optJSONArray("bms")
        if (bms != null) for (k in 0 until bms.length()) {
            val b = bms.getJSONObject(k)
            p.bookmarks.add(Bm(b.getInt("l"), b.optString("n", "")))
        }
        p.rebuildBm()
        val kind = st.optString("kind", "none")
        val ref = st.optString("ref", "")
        val tgt = st.optString("target", "")
        p.fileName = st.optString("name", "")
        val savedSize = st.optLong("size", 0L)
        val cl = st.optInt("cl", 0); val cc = st.optInt("cc", 0); val top = st.optInt("top", 0)
        val pieces = st.optJSONArray("pieces")
        val d = Doc()
        d.eol = if (st.optBoolean("crlf", false)) "\r\n" else "\n"
        if (tgt.isNotEmpty()) d.target = Uri.parse(tgt)
        var lastMod = 0L
        if (kind == "uri" && ref.isNotEmpty()) {
            val u = Uri.parse(ref)
            try {
                d.src = openUriSrc(this, u); d.srcKind = "uri"; d.srcRef = ref
                lastMod = queryLastMod(u)
            } catch (e: Exception) { toast("⚠ Cannot re-open " + p.fileName); d.src = null }
        } else if (kind == "file" && ref.isNotEmpty() && File(ref).exists()) {
            d.src = openFileSrc(File(ref)); d.srcKind = "file"; d.srcRef = ref
        }
        p.replaceDoc(d)
        val apply: () -> Unit = {
            val sr = d.src
            if (pieces != null && (sr == null || sr.size == savedSize)) {
                val list = ArrayList<Piece>()
                var ok = true
                for (k in 0 until pieces.length()) {
                    val po = pieces.getJSONObject(k)
                    if (po.getString("t") == "o") {
                        val s0 = po.getInt("s"); val c0 = po.getInt("c")
                        if (sr == null || s0 + c0 > d.baseLines) ok = false else list.add(Piece(null, s0, c0))
                    } else {
                        val la = po.getJSONArray("l")
                        val arr = Array(la.length()) { idx -> la.getString(idx) }
                        d.addInline(list, arr)
                    }
                }
                if (ok && list.isNotEmpty()) { d.setState(list); d.modified = true }
            } else if (pieces != null) {
                toast("⚠ File changed on disk — unsaved edits for " + p.fileName + " were dropped")
            }
            v.setCaret(cl, cc, false)
            v.topLine = top
            v.topPx = 0f
            p.onTextChanged()
            v.invalidate()
            updateStatus()
        }
        if (d.src != null) {
            d.afterIndex = apply
            d.beginIndex(ui, cacheDir, lastMod)
        } else {
            apply()
        }
    }

    // ───────── hardware keyboard shortcuts ─────────
    fun handleKey(e: KeyEvent, focus: View?): Boolean {
        if (e.action != KeyEvent.ACTION_DOWN) return false
        val ctrl = e.isCtrlPressed
        val shift = e.isShiftPressed
        val k = e.keyCode
        val inField = focus is EditText
        if (k == KeyEvent.KEYCODE_F2) { bmNext(!shift); return true }
        if (ctrl) {
            if (inField && (k == KeyEvent.KEYCODE_C || k == KeyEvent.KEYCODE_X || k == KeyEvent.KEYCODE_V ||
                    k == KeyEvent.KEYCODE_A || k == KeyEvent.KEYCODE_Z || k == KeyEvent.KEYCODE_Y)) {
                return false
            }
            val p = cur
            when (k) {
                KeyEvent.KEYCODE_T -> { if (shift) toggleFloat() else newPane(); return true }
                KeyEvent.KEYCODE_O -> { openFiles(shift); return true }
                KeyEvent.KEYCODE_S -> { if (p != null) { if (shift) saveAs(p, null) else savePane(p, null) }; return true }
                KeyEvent.KEYCODE_W -> { closeCurrentTab(); return true }
                KeyEvent.KEYCODE_H, KeyEvent.KEYCODE_F -> { if (panelWhich != 1) showPanel(1) else findEt.requestFocus(); return true }
                KeyEvent.KEYCODE_G -> { focusGoto(); return true }
                KeyEvent.KEYCODE_B -> { if (shift) showBookmarks() else if (p != null) toggleBookmarkAt(p, p.view.caretL); return true }
                KeyEvent.KEYCODE_M -> { toggleScm(); return true }
                KeyEvent.KEYCODE_Z -> { p?.view?.doUndo(); return true }
                KeyEvent.KEYCODE_Y -> { p?.view?.doRedo(); return true }
                KeyEvent.KEYCODE_C -> { p?.view?.copySel(false); return true }
                KeyEvent.KEYCODE_X -> { p?.view?.copySel(true); return true }
                KeyEvent.KEYCODE_V -> { p?.view?.paste(); return true }
                KeyEvent.KEYCODE_A -> { p?.view?.selectAll(); return true }
                KeyEvent.KEYCODE_EQUALS, KeyEvent.KEYCODE_PLUS, KeyEvent.KEYCODE_NUMPAD_ADD -> { zoomBy(1); return true }
                KeyEvent.KEYCODE_MINUS, KeyEvent.KEYCODE_NUMPAD_SUBTRACT -> { zoomBy(-1); return true }
                KeyEvent.KEYCODE_TAB -> { nextTab(if (shift) -1 else 1); return true }
                else -> { }
            }
        }
        return false
    }

    override fun dispatchKeyEvent(e: KeyEvent): Boolean {
        if (handleKey(e, currentFocus)) return true
        return super.dispatchKeyEvent(e)
    }

    // ═══════════════ floating / always-on-top window mode ═══════════════
    var overlayOn = false
    var ovLp: WindowManager.LayoutParams? = null
    private var ovWm: WindowManager? = null
    private var ovFrame: OvFrame? = null
    private var ovBody: FrameLayout? = null
    private var ovBottom: LinearLayout? = null
    private var ovLeft: View? = null
    private var ovRight: View? = null
    private var ovTypeBtn: Button? = null
    private var ovAlphaBtn: Button? = null
    private var ovCollapsed = false
    private var ovTyping = true
    private var ovSavedH = 0
    private var ovAlphaIdx = 0
    private var skipAutoDock = false
    private val ovAlphas = floatArrayOf(1.0f, 0.85f, 0.7f, 0.5f)

    /** context for dialogs: while floating, the activity is in the background, so dialogs must be overlay windows */
    fun dctx(): Context = if (overlayOn) applicationContext else this

    fun prepDialog(d: AlertDialog) {
        if (overlayOn) d.window?.setType(WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY)
    }

    fun panelOpen(): Boolean = panelWhich != 0

    fun toggleFloat() {
        if (overlayOn) exitFloat(true) else enterFloat()
    }

    private fun ovSetIcon(v: View, type: Int) {
        try { v.pointerIcon = PointerIcon.getSystemIcon(this, type) } catch (e: Exception) { }
    }

    private fun mkGrip(mask: Int, color: Int, icon: Int, label: String): TextView {
        val t = TextView(this)
        t.text = label
        t.setTextColor(cWhite)
        t.textSize = 9f
        t.gravity = Gravity.CENTER
        t.setBackgroundColor(color)
        t.setOnTouchListener(OvTouch(this, mask))
        ovSetIcon(t, icon)
        return t
    }

    fun enterFloat() {
        if (overlayOn) return
        if (!Settings.canDrawOverlays(this)) {
            toast("Turn ON \"Allow display over other apps\" for this app, come back and tap Float again")
            try {
                startActivity(Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION, Uri.parse("package:$packageName")))
            } catch (e: Exception) {
                toast("Open Settings > Apps > Big Notepad > Display over other apps")
            }
            return
        }
        val wm = applicationContext.getSystemService(Context.WINDOW_SERVICE) as WindowManager
        val dm = resources.displayMetrics
        val sp = getSharedPreferences("floatwin", Context.MODE_PRIVATE)
        val sw = dm.widthPixels
        val sh = dm.heightPixels
        var w = sp.getInt("w", minOf((sw * 0.92f).toInt(), dp(440)))
        var h = sp.getInt("h", (sh * 0.55f).toInt())
        w = w.coerceIn(dp(240), maxOf(dp(240), sw))
        h = h.coerceIn(dp(160), maxOf(dp(160), sh))
        var x = sp.getInt("x", (sw - w) / 2)
        var y = sp.getInt("y", dp(48))
        x = x.coerceIn(-(w - dp(70)), sw - dp(70))
        y = y.coerceIn(0, maxOf(0, sh - dp(40)))
        ovAlphaIdx = sp.getInt("a", 0).coerceIn(0, ovAlphas.size - 1)
        ovTyping = true
        ovCollapsed = false
        ovSavedH = h

        val f = OvFrame(this, this)
        f.orientation = LinearLayout.HORIZONTAL
        f.setBackgroundColor(0xFF007ACC.toInt())
        val gl = mkGrip(1, 0xFF007ACC.toInt(), PointerIcon.TYPE_HORIZONTAL_DOUBLE_ARROW, "")
        val gr = mkGrip(2, 0xFF007ACC.toInt(), PointerIcon.TYPE_HORIZONTAL_DOUBLE_ARROW, "")
        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL
        col.setBackgroundColor(cBg)

        // title bar = drag handle + buttons
        val bar = LinearLayout(this)
        bar.orientation = LinearLayout.HORIZONTAL
        bar.gravity = Gravity.CENTER_VERTICAL
        bar.setBackgroundColor(0xFF37374F.toInt())
        bar.setPadding(dp(4), dp(1), dp(4), dp(1))
        bar.setOnTouchListener(OvTouch(this, 0))
        ovSetIcon(bar, PointerIcon.TYPE_ALL_SCROLL)
        val ttl = mkTv("📌 Big Notepad  (drag here to move)", cWhite, 11f)
        ttl.setSingleLine(true)
        bar.addView(ttl, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        val gc = 0xFF4A4A6A.toInt()
        val bTool = mkBtn("▤", gc, cWhite) {
            toolbarBox.visibility = if (toolbarBox.visibility == View.VISIBLE) View.GONE else View.VISIBLE
        }
        val bType = mkBtn("⌨ On", 0xFF27AE60.toInt(), cWhite) { ovToggleTyping() }
        val bAlpha = mkBtn("◐", gc, cWhite) { ovCycleAlpha() }
        val bCol = mkBtn("▁", gc, cWhite) { ovToggleCollapse() }
        val bFull = mkBtn("⤢", 0xFF2980B9.toInt(), cWhite) { exitFloat(true) }
        ovTypeBtn = bType
        ovAlphaBtn = bAlpha
        for (b in listOf(bTool, bType, bAlpha, bCol, bFull)) {
            bar.addView(b, lp(ViewGroup.LayoutParams.WRAP_CONTENT, dp(26), 0f, 1))
        }

        // body: the whole notepad UI
        val body = FrameLayout(this)
        body.setBackgroundColor(cBg)
        (root.parent as? ViewGroup)?.removeView(root)
        body.addView(root, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))

        // bottom resize bar (corners + bottom edge)
        val bottom = LinearLayout(this)
        bottom.orientation = LinearLayout.HORIZONTAL
        val bl = mkGrip(5, 0xFF2B8AD6.toInt(), PointerIcon.TYPE_TOP_RIGHT_DIAGONAL_DOUBLE_ARROW, "◣")
        val bm = mkGrip(4, 0xFF005A9E.toInt(), PointerIcon.TYPE_VERTICAL_DOUBLE_ARROW, "▬▬ resize ▬▬")
        val br = mkGrip(6, 0xFF2B8AD6.toInt(), PointerIcon.TYPE_TOP_LEFT_DIAGONAL_DOUBLE_ARROW, "◢")
        bottom.addView(bl, LinearLayout.LayoutParams(dp(40), dp(18)))
        bottom.addView(bm, LinearLayout.LayoutParams(0, dp(18), 1f))
        bottom.addView(br, LinearLayout.LayoutParams(dp(40), dp(18)))

        col.addView(bar, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        col.addView(body, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
        col.addView(bottom, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        f.addView(gl, LinearLayout.LayoutParams(dp(10), ViewGroup.LayoutParams.MATCH_PARENT))
        f.addView(col, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f))
        f.addView(gr, LinearLayout.LayoutParams(dp(10), ViewGroup.LayoutParams.MATCH_PARENT))

        val lp0 = WindowManager.LayoutParams(
            w, h, WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL, PixelFormat.TRANSLUCENT)
        lp0.gravity = Gravity.TOP or Gravity.START
        lp0.x = x
        lp0.y = y
        lp0.alpha = ovAlphas[ovAlphaIdx]
        lp0.softInputMode = WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE
        lp0.title = "BigNotepadFloat"
        try {
            wm.addView(f, lp0)
        } catch (e: Exception) {
            body.removeView(root)
            setContentView(root)
            toast("❌ Cannot show floating window: " + (e.message ?: e.toString()))
            return
        }
        ovWm = wm
        ovLp = lp0
        ovFrame = f
        ovBody = body
        ovBottom = bottom
        ovLeft = gl
        ovRight = gr
        overlayOn = true
        ovUpdateAlphaBtn()
        try { startForegroundService(Intent(this, FloatKeepService::class.java)) } catch (e: Exception) { }
        ui.postDelayed({ cur?.view?.requestFocus() }, 100)
        toast("📌 Floating: drag the title bar to move, drag edges/corners to resize, ⤢ = full app")
        ui.postDelayed({ if (overlayOn) moveTaskToBack(true) }, 300)
    }

    fun exitFloat(bringFront: Boolean) {
        if (!overlayOn) return
        saveOvGeom()
        val f = ovFrame
        try { ovBody?.removeView(root) } catch (e: Exception) { }
        try { if (f != null) ovWm?.removeView(f) } catch (e: Exception) { }
        ovFrame = null
        ovBody = null
        ovBottom = null
        ovLeft = null
        ovRight = null
        ovLp = null
        overlayOn = false
        try { stopService(Intent(this, FloatKeepService::class.java)) } catch (e: Exception) { }
        setContentView(root)
        toolbarBox.visibility = View.VISIBLE
        cur?.view?.requestFocus()
        if (bringFront) {
            try {
                val i = Intent(this, MainActivity::class.java)
                i.addFlags(Intent.FLAG_ACTIVITY_REORDER_TO_FRONT)
                startActivity(i)
            } catch (e: Exception) { }
        }
        sessionDirty = true
        updateStatus()
    }

    private fun killOverlay() {
        if (!overlayOn) return
        try { ovBody?.removeView(root) } catch (e: Exception) { }
        try { val f = ovFrame; if (f != null) ovWm?.removeView(f) } catch (e: Exception) { }
        ovFrame = null
        ovBody = null
        ovBottom = null
        ovLeft = null
        ovRight = null
        ovLp = null
        overlayOn = false
        try { stopService(Intent(this, FloatKeepService::class.java)) } catch (e: Exception) { }
    }

    fun saveOvGeom() {
        val lp = ovLp ?: return
        val ed = getSharedPreferences("floatwin", Context.MODE_PRIVATE).edit()
        ed.putInt("x", lp.x)
        ed.putInt("y", lp.y)
        ed.putInt("w", lp.width)
        ed.putInt("h", if (ovCollapsed) ovSavedH else lp.height)
        ed.putInt("a", ovAlphaIdx)
        ed.apply()
    }

    /** mask: 0 = move window; bit1 = left edge, bit2 = right edge, bit4 = bottom edge */
    fun ovApply(mask: Int, ox: Int, oy: Int, ow: Int, oh: Int, dx: Int, dy: Int) {
        val lp = ovLp ?: return
        val f = ovFrame ?: return
        val dm = resources.displayMetrics
        val sw = dm.widthPixels
        val sh = dm.heightPixels
        if (mask == 0) {
            lp.x = (ox + dx).coerceIn(-(lp.width - dp(70)), sw - dp(70))
            lp.y = (oy + dy).coerceIn(0, maxOf(0, sh - dp(40)))
        } else {
            val minW = dp(240)
            val minH = dp(160)
            var nx = ox
            var nw = ow
            var nh = oh
            if ((mask and 2) != 0) nw = maxOf(minW, minOf(ow + dx, maxOf(minW, sw - ox)))
            if ((mask and 1) != 0) {
                nw = maxOf(minW, ow - dx)
                nx = ox + ow - nw
                if (nx < 0) { nx = 0; nw = maxOf(minW, ox + ow) }
            }
            if ((mask and 4) != 0) nh = maxOf(minH, minOf(oh + dy, maxOf(minH, sh - oy)))
            lp.x = nx
            lp.width = nw
            if ((mask and 4) != 0 && !ovCollapsed) lp.height = nh
        }
        try { ovWm?.updateViewLayout(f, lp) } catch (e: Exception) { }
    }

    fun ovDone() {
        val lp = ovLp ?: return
        if (!ovCollapsed) ovSavedH = lp.height
        saveOvGeom()
    }

    private fun ovToggleCollapse() {
        val lp = ovLp ?: return
        val f = ovFrame ?: return
        ovCollapsed = !ovCollapsed
        val vis = if (ovCollapsed) View.GONE else View.VISIBLE
        ovBody?.visibility = vis
        ovBottom?.visibility = vis
        ovLeft?.visibility = vis
        ovRight?.visibility = vis
        if (ovCollapsed) {
            ovSavedH = lp.height
            lp.height = WindowManager.LayoutParams.WRAP_CONTENT
        } else {
            lp.height = ovSavedH
        }
        try { ovWm?.updateViewLayout(f, lp) } catch (e: Exception) { }
        saveOvGeom()
    }

    private fun ovCycleAlpha() {
        val lp = ovLp ?: return
        val f = ovFrame ?: return
        ovAlphaIdx = (ovAlphaIdx + 1) % ovAlphas.size
        lp.alpha = ovAlphas[ovAlphaIdx]
        try { ovWm?.updateViewLayout(f, lp) } catch (e: Exception) { }
        ovUpdateAlphaBtn()
        saveOvGeom()
    }

    private fun ovUpdateAlphaBtn() {
        ovAlphaBtn?.text = "◐ " + Math.round(ovAlphas[ovAlphaIdx] * 100f) + "%"
    }

    /** Typing ON: the window takes the keyboard. Typing OFF: the window stays on top but other apps keep the keyboard. */
    private fun ovToggleTyping() {
        val lp = ovLp ?: return
        val f = ovFrame ?: return
        ovTyping = !ovTyping
        lp.flags = if (ovTyping) (lp.flags and WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE.inv())
        else (lp.flags or WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE)
        try { ovWm?.updateViewLayout(f, lp) } catch (e: Exception) { }
        ovTypeBtn?.text = if (ovTyping) "⌨ On" else "⌨ Off"
        ovTypeBtn?.background = roundBg(if (ovTyping) 0xFF27AE60.toInt() else 0xFF7F8C8D.toInt(), 5)
        val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        if (ovTyping) {
            cur?.view?.let { it.requestFocus(); it.showKeyboard() }
            toast("Typing ON: this window uses the keyboard")
        } else {
            imm.hideSoftInputFromWindow(f.windowToken, 0)
            toast("Typing OFF: other apps get the keyboard; this window stays on top")
        }
    }
}

// ═══════════════════════════ dialog builder (works while floating) ═══════════════════════════
class DBuilder(val app: MainActivity) : AlertDialog.Builder(app.dctx()) {
    override fun create(): AlertDialog {
        val d = super.create()
        app.prepDialog(d)
        return d
    }
}

// ═══════════════════════════ floating window root (keys + back) ═══════════════════════════
class OvFrame(ctx: Context, val app: MainActivity) : LinearLayout(ctx) {
    override fun dispatchKeyEvent(e: KeyEvent): Boolean {
        if (e.keyCode == KeyEvent.KEYCODE_BACK) {
            if (e.action == KeyEvent.ACTION_UP && app.panelOpen()) { app.showPanel(0); return true }
            return super.dispatchKeyEvent(e)
        }
        if (app.handleKey(e, findFocus())) return true
        return super.dispatchKeyEvent(e)
    }
}

// ═══════════════════════════ drag / resize handler (finger or mouse) ═══════════════════════════
class OvTouch(val app: MainActivity, val mask: Int) : View.OnTouchListener {
    private var sx = 0f
    private var sy = 0f
    private var ox = 0
    private var oy = 0
    private var ow = 0
    private var oh = 0
    override fun onTouch(v: View, ev: MotionEvent): Boolean {
        val lp = app.ovLp ?: return false
        when (ev.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                sx = ev.rawX; sy = ev.rawY
                ox = lp.x; oy = lp.y; ow = lp.width; oh = lp.height
            }
            MotionEvent.ACTION_MOVE -> {
                app.ovApply(mask, ox, oy, ow, oh, (ev.rawX - sx).toInt(), (ev.rawY - sy).toInt())
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> app.ovDone()
            else -> { }
        }
        return true
    }
}

// ═══════════════════════════ keeps the process alive while floating ═══════════════════════════
class FloatKeepService : Service() {
    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        val chId = "float_keep"
        val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        nm.createNotificationChannel(NotificationChannel(chId, "Floating notepad", NotificationManager.IMPORTANCE_LOW))
        val open = Intent(this, MainActivity::class.java)
        open.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_REORDER_TO_FRONT)
        val pi = PendingIntent.getActivity(this, 0, open, PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT)
        val n = Notification.Builder(this, chId)
            .setSmallIcon(android.R.drawable.ic_menu_edit)
            .setContentTitle("Big Notepad is floating")
            .setContentText("Tap to return to the full app")
            .setContentIntent(pi)
            .setOngoing(true)
            .build()
        if (Build.VERSION.SDK_INT >= 34) startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_SPECIAL_USE)
        else startForeground(1, n)
        return START_NOT_STICKY
    }
}
