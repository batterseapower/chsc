{-# LANGUAGE ForeignFunctionInterface #-}
module IGraph (Color, subgraphIsomorphisms) where

import Utilities

import Control.Exception (bracket)

import Data.Array
import Data.IORef
import qualified Data.Map as M

import Foreign.C
import Foreign.Marshal
import Foreign.Ptr

import qualified Data.Graph.Wrapper as G
import qualified Data.Graph.Wrapper.Internal as G


type Color = Int

subgraphIsomorphisms :: Ord a => G.Graph a Color -> G.Graph a Color -> [M.Map a a]
subgraphIsomorphisms g_smaller g_larger = [M.fromList [(i_smaller, G.indexGVertexArray g_larger ! n_larger) | (i_smaller, n_larger) <- fromJust (elems (G.indexGVertexArray g_smaller) `zipEqual` raw_subiso)] | raw_subiso <- raw_subisos]
  where
    raw_subisos = subgraphIsomorphisms' [(G.gVertexVertexArray g_smaller ! m, ns) | (m, ns) <- assocs (G.graph g_smaller)]
                                        [(G.gVertexVertexArray g_larger  ! m, ns) | (m, ns) <- assocs (G.graph g_larger)]



type Callback = Ptr CDouble -> IO CInt

foreign import ccall "wrapper" mkCallback :: Callback -> IO (FunPtr Callback)

foreign import ccall find_graph_subisomorphisms :: CInt -> Ptr CInt -> CInt -> Ptr CDouble
                                                -> CInt -> Ptr CInt -> CInt -> Ptr CDouble
                                                -> FunPtr Callback
                                                -> IO ()

type OutgoingEdges = [Int]
type AdjacencyList = [(Color, OutgoingEdges)]
type Subisomorphism = [Int]

subgraphIsomorphisms' :: AdjacencyList -> AdjacencyList -> [Subisomorphism]
subgraphIsomorphisms' g_smaller g_larger
  = unsafeLocalState $ withArray (map (fromIntegral . fst) g_smaller) $ \smaller_colors ->
                       withArray (map (fromIntegral . fst) g_larger) $ \larger_colors ->
                       withArray [fromIntegral i | (from, tos) <- [0..] `zip` map snd g_smaller, to <- tos, i <- [from, to]] $ \smaller_edges ->
                       withArray [fromIntegral i | (from, tos) <- [0..] `zip` map snd g_larger, to <- tos, i <- [from, to]] $ \larger_edges -> do
                           isos <- newIORef []
                           let callback mapping_ptr = do
                                  mapping <- peekArray (genericLength g_smaller) mapping_ptr
                                  modifyIORef isos (map (round :: CDouble -> Int) mapping :)
                                  return 1
                           bracket (mkCallback callback) freeHaskellFunPtr $ \callback ->
                              find_graph_subisomorphisms (genericLength g_smaller) smaller_colors (genericLength (concatMap snd g_smaller)) smaller_edges
                                                         (genericLength g_larger)  larger_colors  (genericLength (concatMap snd g_larger))  larger_edges
                                                         callback
                           readIORef isos
