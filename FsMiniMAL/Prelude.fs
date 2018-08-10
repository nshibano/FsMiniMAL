module FsMiniMAL.Prelude

let prelude = """
fun list_append l1 l2 =
  case (l1, l2) of
  | (h1 :: t1, l2) -> h1 :: list_append t1 l2
  | ([], l2) -> l2;

fun option_may f opt =
  case opt of
  | Some x -> f x
  | None -> ()

fun option_map f opt =
  case opt of
  | Some x -> Some (f x)
  | None -> None

fun ref x = { contents = x }
fun ref_set r x = r.contents <- x
fun ref_get r = r.contents

val length = array_length
val add = array_add

fun array_map f a =
  begin
    val accu = [||];
    for i = 0 to length a - 1 do
      add accu (f a.[i]);
    accu
  end

fun array_init n f =
  begin
    val accu = [||];
    for i = 0 to n - 1 do
      add accu (f i);
    accu
  end;

fun array_iter (f : 'a -> unit) (a : 'a array) =
  for i = 0 to array_length a - 1 do
    f a.[i];

fun string_map_to_array f s =
  begin
    val accu = [||];
    for i = 0 to string_length s - 1 do
      accu << f s.[i];
    accu
  end;

fun id x = x;
fun ignore x = ();

fun kprintfn k fmt = kprintf (fn s -> k ((s : string) ^ "\r\n")) fmt;
fun printf fmt = kprintf print_string fmt;
fun printfn fmt = kprintfn print_string fmt;
fun sprintf fmt = kprintf id fmt;
fun sprintfn fmt = kprintfn id fmt;
      
fun list_length l =
  case l of
  | [] -> 0
  | h :: t -> 1 + list_length t

fun list_head l = case l of h :: _ -> h

fun failwith msg = raise (Failure msg)

fun min a b = if compare a b = -1 then a else b
fun max a b = if compare a b =  1 then a else b

// translated from stable_sort in https://github.com/ocaml/ocaml/blob/trunk/stdlib/array.ml   
fun sort cmp a =
  begin
    fun merge src1ofs src1len src2 src2ofs src2len dst dstofs =
      begin
        val src1r = src1ofs + src1len and src2r = src2ofs + src2len;
        fun loop i1 s1 i2 s2 d =
          if cmp s1 s2 <= 0 then
            begin
              dst.[d] <- s1;
              val i1 = i1 + 1;
              if i1 < src1r then
                loop i1 a.[i1] i2 s2 (d + 1)
              else
                array_blit src2 i2 dst (d + 1) (src2r - i2)
            end
          else
            begin
              dst.[d] <- s2;
              val i2 = i2 + 1;
              if i2 < src2r then
                loop i1 s1 i2 src2.[i2] (d + 1)
              else
                array_blit a i1 dst (d + 1) (src1r - i1)
            end;
        loop src1ofs a.[src1ofs] src2ofs src2.[src2ofs] dstofs;
      end;
    fun isortto srcofs dst dstofs len =
      for i = 0 to len - 1 do
        begin
          val e = a.[srcofs + i];
          var j = dstofs + i - 1;
          while (j >= dstofs && cmp dst.[j] e > 0) do
            begin
              dst.[j + 1] <- dst.[j];
              j <- j - 1;
            end;
          dst.[j + 1] <- e;
        end;
    val cutoff = 5;
    fun sortto srcofs dst dstofs len =
      if len <= cutoff then isortto srcofs dst dstofs len
      else
        begin
          val l1 = len / 2;
          val l2 = len - l1;
          sortto (srcofs + l1) dst (dstofs + l1) l2;
          sortto srcofs a (srcofs + l2) l1;
          merge (srcofs + l2) l1 dst (dstofs + l1) l2 dst dstofs;
        end;
    val l = length a;
    if l <= cutoff then isortto 0 a 0 l
    else
      begin
        val l1 = l / 2;
        val l2 = l - l1;
        val t = array_create l2 a.[0];
        sortto l1 t 0 l2;
        sortto 0 a l2 l1;
        merge l2 l1 t 0 l2 a 0;
      end
  end;

fun lexbuf_of_string s = { source = s, start_pos = 0, end_pos = 0, scan_start_pos = 0, eof = false };
"""