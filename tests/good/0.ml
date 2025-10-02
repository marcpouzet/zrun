(* The Zelus compiler, version 2024-dev
  (2025-05-13-5:25) *)
open Ztypes
let (g, f) =
      let rec g_11 n_12 =
              (fun (x_13) ->
                (match n_12 with
                   | 0 -> self_18.r_17 <- 0
                   | _ ->
                       self_18.r_17 <- (+) 1
                                           ((f_10 ((-) n_12 1)) ((+) x_13 1))
                   ); self_18.r_17)
              and f_10 n_14 = (fun (x_15) -> (g_11 ((-) n_14 1)) x_15)  in
      (g_11, f_10)
let (main1) = let main1_16 = (fun _ -> (g 10000) 1) in
              main1_16
