#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FLAPPY PY - um clone de Flappy Bird feito em Python + Pygame
============================================================

Como executar
-------------
    pip install pygame
    python flappy_py.py

Controles
---------
    ESPAÇO / SETA PARA CIMA / W / clique do mouse / toque na tela ... pular
    Mobile: a tela inteira funciona como botão de toque
    P ou ESC ........ pausar / continuar (no menu, ESC fecha o jogo)
    ENTER / R ....... jogar de novo (na tela de game over)
    M ............... ligar / desligar o som
    F11 ............. tela cheia

Características
---------------
    * Nenhum arquivo externo: gráficos e sons são gerados por código.
    * Física independente da taxa de quadros (usa "delta time").
    * Canos gerados proceduralmente, sempre com passagem alcançável.
    * Dificuldade progressiva (velocidade sobe e a abertura diminui).
    * Colisão precisa (círculo x retângulo) com canos, chão e teto.
    * Estados de jogo: MENU, PLAYING, PAUSED, DYING e GAME_OVER.
    * Recorde salvo em disco, medalhas, partículas, tremor de tela e sons.

Organização do código (cada seção é independente)
-------------------------------------------------
    1. Configurações ............ constantes que controlam todo o jogo
    2. Funções auxiliares ....... matemática, colisão, dificuldade
    3. Áudio .................... sons sintetizados por código
    4. Recorde .................. leitura/gravação da maior pontuação
    5. Recursos gráficos ........ todos os sprites são desenhados aqui
    6. Texto .................... renderização de texto com contorno
    7. Entidades ................ Pássaro, Cano, Partícula, Chão, Fundo
    8. Jogo ..................... máquina de estados e laço principal
"""

from __future__ import annotations

import array
import asyncio
import json
import math
import random
import sys
from enum import Enum, auto
from pathlib import Path
from typing import Dict, List, Optional, Tuple

try:
    import pygame
except ImportError:  # Mensagem amigável caso o Pygame não esteja instalado
    sys.exit("Pygame não encontrado.\nInstale com:  pip install pygame")

Color = Tuple[int, int, int]
Rect4 = Tuple[float, float, float, float]  # (x, y, largura, altura)


# =============================================================================
# 1. CONFIGURAÇÕES
# =============================================================================
# Janela ----------------------------------------------------------------------
WIDTH, HEIGHT = 400, 640
FPS = 60
MAX_DT = 1 / 30          # limite do delta time (evita "teleportes" se o jogo travar)
TITLE = "Flappy Py"

# Chão ------------------------------------------------------------------------
GROUND_HEIGHT = 100
GROUND_Y = HEIGHT - GROUND_HEIGHT   # coordenada Y onde o chão começa
GROUND_PERIOD = 24                  # largura do padrão do chão que se repete

# Pássaro (valores de física em pixels e segundos) -----------------------------
BIRD_X = 110                 # posição horizontal fixa do pássaro
BIRD_START_Y = 290
BIRD_SIZE = (44, 34)         # tamanho do sprite
BIRD_RADIUS = 12             # raio da hitbox (menor que o sprite = mais justo)
GRAVITY = 1700.0             # aceleração para baixo (px/s²)
FLAP_VELOCITY = -460.0       # velocidade instantânea do pulo (px/s, negativo = sobe)
MAX_FALL_SPEED = 720.0       # velocidade terminal de queda

# Canos -----------------------------------------------------------------------
PIPE_WIDTH = 72
PIPE_CAP_HEIGHT = 30         # altura da "boca" do cano
PIPE_CAP_OVERHANG = 4        # quanto a boca sobra de cada lado do corpo
PIPE_CAP_WIDTH = PIPE_WIDTH + 2 * PIPE_CAP_OVERHANG
PIPE_SPACING = 245           # distância horizontal entre dois canos consecutivos
PIPE_MIN_MARGIN = 70         # espaço mínimo entre a abertura e o teto/chão
PIPE_MAX_SHIFT = 130         # variação máxima do centro da abertura entre canos (garante justiça)
FIRST_PIPE_X = WIDTH + 60    # onde nasce o primeiro cano

# Dificuldade progressiva ------------------------------------------------------
BASE_SPEED = 170.0           # velocidade inicial do mundo (px/s)
MAX_SPEED = 240.0
SPEED_PER_POINT = 2.5
BASE_GAP = 165.0             # tamanho inicial da abertura entre os canos
MIN_GAP = 135.0
GAP_SHRINK_PER_POINT = 1.0

# Tempos de interface (segundos) -------------------------------------------------
RESTART_DELAY = 0.45         # bloqueio curto após morrer (evita reinício acidental)
RESUME_COUNTDOWN = 1.5       # contagem 3-2-1 ao sair da pausa
SHAKE_TIME = 0.35
FLASH_TIME = 0.30
SCORE_POP_TIME = 0.15
PANEL_SLIDE_TIME = 0.55

# Áudio -------------------------------------------------------------------------
SAMPLE_RATE = 44100

# Cores -------------------------------------------------------------------------
WHITE: Color = (255, 255, 255)
OUTLINE: Color = (83, 56, 71)        # marrom-escuro usado nos contornos
YELLOW: Color = (255, 214, 70)
ORANGE: Color = (240, 120, 40)
RED: Color = (225, 70, 55)
SKY_TOP: Color = (78, 192, 237)
SKY_BOTTOM: Color = (196, 236, 250)
DIRT_TOP: Color = (226, 220, 152)
DIRT_BOTTOM: Color = (203, 190, 118)
GRASS_A: Color = (115, 191, 46)
GRASS_B: Color = (150, 226, 70)
GRASS_DARK: Color = (84, 140, 30)
PANEL_BG: Color = (236, 228, 168)

# Medalhas: (pontos mínimos, nome, cor base, cor de brilho) — da maior para a menor
MEDALS = (
    (40, "Platina", (200, 225, 235), (245, 252, 255)),
    (30, "Ouro", (240, 190, 40), (255, 232, 130)),
    (20, "Prata", (190, 195, 205), (240, 242, 248)),
    (10, "Bronze", (205, 127, 60), (240, 180, 120)),
)

# Eventos que podem não existir em versões antigas do Pygame --------------------
FINGERDOWN = getattr(pygame, "FINGERDOWN", -1)
WINDOWFOCUSLOST = getattr(pygame, "WINDOWFOCUSLOST", -2)


class State(Enum):
    """Estados possíveis do jogo (máquina de estados)."""
    MENU = auto()       # tela inicial
    PLAYING = auto()    # partida em andamento
    PAUSED = auto()     # partida congelada
    DYING = auto()      # pássaro bateu em um cano e está caindo
    GAME_OVER = auto()  # painel final com pontuação e opção de reiniciar


# =============================================================================
# 2. FUNÇÕES AUXILIARES
# =============================================================================
def clamp(value: float, low: float, high: float) -> float:
    """Limita `value` ao intervalo [low, high]."""
    return max(low, min(high, value))


def lerp(a: float, b: float, t: float) -> float:
    """Interpolação linear entre a e b."""
    return a + (b - a) * t


def lerp_color(c1: Color, c2: Color, t: float) -> Color:
    """Interpola duas cores RGB (t entre 0 e 1)."""
    t = clamp(t, 0.0, 1.0)
    return (int(lerp(c1[0], c2[0], t)),
            int(lerp(c1[1], c2[1], t)),
            int(lerp(c1[2], c2[2], t)))


def ease_out_cubic(t: float) -> float:
    """Suavização: começa rápido e desacelera no final (usada nas animações)."""
    t = clamp(t, 0.0, 1.0)
    return 1.0 - (1.0 - t) ** 3


def circle_rect_collision(cx: float, cy: float, radius: float, rect: Rect4) -> bool:
    """
    Colisão exata entre um círculo e um retângulo.

    Encontra o ponto do retângulo mais próximo do centro do círculo e verifica
    se a distância até ele é menor que o raio. Funciona para todos os casos
    (círculo tocando lado, quina ou totalmente dentro do retângulo).
    """
    x, y, w, h = rect
    nearest_x = clamp(cx, x, x + w)
    nearest_y = clamp(cy, y, y + h)
    dx, dy = cx - nearest_x, cy - nearest_y
    return dx * dx + dy * dy < radius * radius


def rounded_rect(surface, color: Color, rect, radius: int, width: int = 0) -> None:
    """Retângulo com cantos arredondados (com alternativa para Pygame antigo)."""
    try:
        pygame.draw.rect(surface, color, rect, width, border_radius=radius)
    except TypeError:
        pygame.draw.rect(surface, color, rect, width)


def pipe_speed(score: int) -> float:
    """Velocidade do mundo em função da pontuação (aumenta devagar até o limite)."""
    return min(MAX_SPEED, BASE_SPEED + score * SPEED_PER_POINT)


def pipe_gap(score: int) -> float:
    """Tamanho da abertura entre os canos (diminui devagar até o limite)."""
    return max(MIN_GAP, BASE_GAP - score * GAP_SHRINK_PER_POINT)


def medal_for(score: int):
    """Retorna a medalha correspondente à pontuação, ou None se não houver."""
    for medal in MEDALS:
        if score >= medal[0]:
            return medal
    return None


# =============================================================================
# 3. ÁUDIO (sons sintetizados — sem arquivos externos)
# =============================================================================
def synth(f0: float, f1: float, duration: float, volume: float = 0.3,
          wave: str = "sine", rate: int = SAMPLE_RATE) -> "array.array":
    """
    Gera um som simples.

    f0 -> f1 : frequência inicial e final (varredura de tom, em Hz)
    wave     : "sine" (suave), "square" (retrô) ou "noise" (ruído/impacto)
    """
    total = max(1, int(rate * duration))
    attack = max(1, int(rate * 0.004))      # 4 ms de entrada para evitar "estalos"
    samples = array.array("h")
    phase = 0.0
    for i in range(total):
        t = i / total
        phase += 2.0 * math.pi * (f0 + (f1 - f0) * t) / rate
        if wave == "square":
            raw = 1.0 if math.sin(phase) >= 0.0 else -1.0
        elif wave == "noise":
            raw = random.uniform(-1.0, 1.0)
        else:
            raw = math.sin(phase)
        envelope = min(1.0, i / attack) * (1.0 - t)   # entrada rápida + decaimento
        samples.append(int(raw * envelope * volume * 32767))
    return samples


class SoundManager:
    """Cria e toca os efeitos sonoros. Se o áudio falhar, o jogo segue mudo."""

    def __init__(self) -> None:
        self.available = False
        self.muted = False
        self._sounds: Dict[str, "pygame.mixer.Sound"] = {}

        info = pygame.mixer.get_init()
        if info is None:
            return
        rate, fmt, channels = info
        # Aceitamos áudio de 16 bits (mono ou estéreo); qualquer outra coisa deixa o jogo mudo
        if fmt not in (-16, 0x8010) or channels not in (1, 2):
            return

        def build(samples: "array.array"):
            if channels == 2:   # duplica cada amostra para os canais esquerdo e direito
                samples = array.array("h", (s for s in samples for _ in (0, 1)))
            return pygame.mixer.Sound(buffer=samples.tobytes())

        try:
            self._sounds = {
                "flap": build(synth(360, 640, 0.10, 0.22, "square", rate)),
                "point": build(synth(880, 880, 0.06, 0.25, "sine", rate)
                               + synth(1320, 1320, 0.12, 0.25, "sine", rate)),
                "hit": build(synth(220, 60, 0.20, 0.45, "noise", rate)),
                "die": build(synth(520, 110, 0.40, 0.25, "square", rate)),
            }
            self.available = True
        except (pygame.error, ValueError, TypeError):
            self._sounds = {}

    def play(self, name: str) -> None:
        if self.available and not self.muted:
            sound = self._sounds.get(name)
            if sound is not None:
                sound.play()

    def toggle_mute(self) -> None:
        self.muted = not self.muted


# =============================================================================
# 4. RECORDE (maior pontuação salva em disco)
# =============================================================================
class HighScore:
    """Guarda a maior pontuação em um pequeno arquivo JSON na pasta do usuário."""

    def __init__(self) -> None:
        try:
            self.path: Optional[Path] = Path.home() / ".flappy_py_highscore.json"
        except (RuntimeError, OSError):
            self.path = None
        self.best = self._load()

    def _load(self) -> int:
        if self.path is None:
            return 0
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
            return max(0, int(data.get("best", 0)))
        except (OSError, ValueError, TypeError, AttributeError):
            return 0    # arquivo inexistente, corrompido ou sem permissão

    def _save(self) -> None:
        if self.path is None:
            return
        try:
            self.path.write_text(json.dumps({"best": self.best}), encoding="utf-8")
        except OSError:
            pass        # sem permissão de escrita: o recorde vale só nesta sessão

    def submit(self, score: int) -> bool:
        """Registra uma pontuação. Retorna True se for um novo recorde."""
        if score > self.best:
            self.best = score
            self._save()
            return True
        return False


# =============================================================================
# 5. RECURSOS GRÁFICOS (todos os sprites são desenhados por código)
# =============================================================================
class Fonts:
    """Carrega as fontes do jogo (usa a fonte padrão se as do sistema faltarem)."""

    FAMILY = "arialblack,impact,verdana,dejavusans,arial"

    def __init__(self) -> None:
        self.title = self._load(54)
        self.score = self._load(54)
        self.heading = self._load(30)
        self.body = self._load(22)
        self.small = self._load(16)

    @staticmethod
    def _load(size: int):
        try:
            return pygame.font.SysFont(Fonts.FAMILY, size)
        except (pygame.error, OSError):
            return pygame.font.Font(None, int(size * 1.2))


class Assets:
    """Cria uma única vez todas as imagens do jogo (evita desenhar a cada quadro)."""

    def __init__(self) -> None:
        self.fonts = Fonts()
        self.sky = self._make_sky()
        self.city = self._make_city()
        self.hills = self._make_hills()
        self.ground = self._make_ground()
        self.clouds = [self._make_cloud(w, h) for w, h in ((92, 38), (128, 50), (70, 30))]
        self.bird_frames = [self._make_bird_frame(dy) for dy in (-5, 0, 5)]
        self.pipe_body, self.pipe_cap_up, self.pipe_cap_down = self._make_pipe_sprites()

    # --- céu ---------------------------------------------------------------
    @staticmethod
    def _make_sky():
        surf = pygame.Surface((WIDTH, HEIGHT))
        for y in range(HEIGHT):
            color = lerp_color(SKY_TOP, SKY_BOTTOM, y / GROUND_Y)
            pygame.draw.line(surf, color, (0, y), (WIDTH, y))
        # Sol com brilho suave (anéis concêntricos translúcidos)
        glow = pygame.Surface((220, 220), pygame.SRCALPHA)
        for radius in range(108, 28, -4):
            alpha = int(10 + 70 * (1 - radius / 108))
            pygame.draw.circle(glow, (255, 250, 205, alpha), (110, 110), radius)
        surf.blit(glow, (300 - 110, 105 - 110))
        pygame.draw.circle(surf, (255, 246, 196), (300, 105), 27)
        return surf.convert()

    # --- camadas de paralaxe (cidade e colinas) ------------------------------
    @staticmethod
    def _make_city():
        height = 170
        surf = pygame.Surface((WIDTH, height), pygame.SRCALPHA)
        rng = random.Random(11)           # semente fixa: a cidade é sempre igual
        wall, window = (168, 214, 232), (196, 232, 244)
        x = 0
        while x < WIDTH - 24:
            w = min(rng.randint(30, 56), WIDTH - 6 - x)   # deixa folga no fim (laço perfeito)
            if w < 20:
                break
            h = rng.randint(50, 150)
            top = height - h
            pygame.draw.rect(surf, wall, (x, top, w, h))
            for wy in range(top + 8, height - 8, 14):     # janelinhas
                for wx in range(x + 6, x + w - 8, 12):
                    pygame.draw.rect(surf, window, (wx, wy, 5, 7))
            x += w + rng.randint(0, 4)
        return surf.convert_alpha()

    @staticmethod
    def _make_hills():
        height = 110
        surf = pygame.Surface((WIDTH, height), pygame.SRCALPHA)
        points = [(0, height)]
        for x in range(0, WIDTH + 1, 4):
            # Duas senoides com períodos inteiros: o fim da imagem encaixa no começo
            y = (52 + 16 * math.sin(2 * math.pi * 2 * x / WIDTH + 0.6)
                 + 7 * math.sin(2 * math.pi * 5 * x / WIDTH + 2.0))
            points.append((x, y))
        points.append((WIDTH, height))
        pygame.draw.polygon(surf, (112, 196, 128), points)
        return surf.convert_alpha()

    # --- chão ------------------------------------------------------------------
    @staticmethod
    def _make_ground():
        width = WIDTH + GROUND_PERIOD * 2          # sobra para a rolagem
        surf = pygame.Surface((width, GROUND_HEIGHT))
        for y in range(GROUND_HEIGHT):             # terra com degradê
            pygame.draw.line(surf, lerp_color(DIRT_TOP, DIRT_BOTTOM, y / GROUND_HEIGHT),
                             (0, y), (width, y))
        pygame.draw.rect(surf, OUTLINE, (0, 0, width, 3))          # contorno superior
        pygame.draw.rect(surf, GRASS_A, (0, 3, width, 14))         # grama
        for x in range(-GROUND_PERIOD, width, GROUND_PERIOD):      # listras inclinadas
            pygame.draw.polygon(surf, GRASS_B, [(x + 12, 3), (x + 24, 3),
                                                (x + 12, 17), (x, 17)])
        pygame.draw.rect(surf, GRASS_DARK, (0, 17, width, 3))      # sombra da grama
        return surf.convert()

    # --- nuvens -----------------------------------------------------------------
    @staticmethod
    def _make_cloud(w: int, h: int):
        surf = pygame.Surface((w, h), pygame.SRCALPHA)
        color = (255, 255, 255, 220)
        pygame.draw.ellipse(surf, color, (0, int(h * 0.45), w, int(h * 0.55)))
        pygame.draw.circle(surf, color, (int(w * 0.30), int(h * 0.55)), int(h * 0.36))
        pygame.draw.circle(surf, color, (int(w * 0.52), int(h * 0.42)), int(h * 0.42))
        pygame.draw.circle(surf, color, (int(w * 0.74), int(h * 0.57)), int(h * 0.32))
        return surf.convert_alpha()

    # --- pássaro ----------------------------------------------------------------
    @staticmethod
    def _make_bird_frame(wing_dy: int):
        """Desenha um quadro do pássaro. `wing_dy` move a asa (animação de bater asas)."""
        w, h = BIRD_SIZE
        surf = pygame.Surface((w, h), pygame.SRCALPHA)
        pygame.draw.ellipse(surf, OUTLINE, (2, 3, 36, 29))              # contorno do corpo
        pygame.draw.ellipse(surf, (250, 205, 50), (4, 5, 32, 25))       # corpo
        pygame.draw.ellipse(surf, (255, 238, 140), (9, 19, 24, 10))     # barriga
        pygame.draw.ellipse(surf, OUTLINE, (28, 13, 16, 15))            # contorno do bico
        pygame.draw.ellipse(surf, RED, (30, 20, 12, 6))                 # bico inferior
        pygame.draw.ellipse(surf, (255, 150, 40), (30, 15, 12, 8))      # bico superior
        pygame.draw.circle(surf, OUTLINE, (29, 11), 8)                  # contorno do olho
        pygame.draw.circle(surf, WHITE, (29, 11), 6)                    # olho
        pygame.draw.circle(surf, OUTLINE, (31, 11), 3)                  # pupila
        pygame.draw.ellipse(surf, OUTLINE, (5, 14 + wing_dy, 22, 15))   # contorno da asa
        pygame.draw.ellipse(surf, (255, 250, 235), (7, 16 + wing_dy, 18, 11))  # asa
        return surf.convert_alpha()

    # --- canos ------------------------------------------------------------------
    @staticmethod
    def _pipe_shade(t: float) -> Color:
        """Cor de uma coluna do cano (t=0 esquerda ... t=1 direita): efeito cilíndrico."""
        light, highlight, dark = (130, 205, 60), (196, 248, 120), (78, 148, 34)
        if t < 0.25:
            return lerp_color(light, highlight, t / 0.25)
        return lerp_color(highlight, dark, (t - 0.25) / 0.75)

    @classmethod
    def _make_pipe_sprites(cls):
        # Corpo do cano: uma coluna alta que será "recortada" na altura necessária
        body = pygame.Surface((PIPE_WIDTH, GROUND_Y))
        for x in range(PIPE_WIDTH):
            pygame.draw.line(body, cls._pipe_shade(x / (PIPE_WIDTH - 1)), (x, 0), (x, GROUND_Y))
        pygame.draw.rect(body, OUTLINE, (0, 0, 3, GROUND_Y))
        pygame.draw.rect(body, OUTLINE, (PIPE_WIDTH - 3, 0, 3, GROUND_Y))

        # Boca do cano (a parte mais larga na ponta)
        cap = pygame.Surface((PIPE_CAP_WIDTH, PIPE_CAP_HEIGHT))
        for x in range(PIPE_CAP_WIDTH):
            pygame.draw.line(cap, cls._pipe_shade(x / (PIPE_CAP_WIDTH - 1)),
                             (x, 0), (x, PIPE_CAP_HEIGHT))
        pygame.draw.rect(cap, OUTLINE, (0, 0, PIPE_CAP_WIDTH, PIPE_CAP_HEIGHT), 3)
        cap_down = pygame.transform.flip(cap, False, True)   # versão para o cano de cima
        return body.convert(), cap.convert(), cap_down.convert()


# =============================================================================
# 6. TEXTO (com contorno e cache para não renderizar tudo a cada quadro)
# =============================================================================
class TextRenderer:
    def __init__(self) -> None:
        self._cache: Dict[tuple, "pygame.Surface"] = {}

    def render(self, text: str, font, color: Color,
               outline_color: Optional[Color], outline: int):
        key = (text, id(font), color, outline_color, outline)
        surf = self._cache.get(key)
        if surf is None:
            base = font.render(text, True, color)
            if outline_color is not None and outline > 0:
                w, h = base.get_size()
                surf = pygame.Surface((w + 2 * outline, h + 2 * outline), pygame.SRCALPHA)
                border = font.render(text, True, outline_color)
                for dx in range(-outline, outline + 1):
                    for dy in range(-outline, outline + 1):
                        if (dx or dy) and dx * dx + dy * dy <= outline * outline + 1:
                            surf.blit(border, (outline + dx, outline + dy))
                surf.blit(base, (outline, outline))
            else:
                surf = base
            if len(self._cache) > 300:      # evita crescer indefinidamente
                self._cache.clear()
            self._cache[key] = surf
        return surf

    def draw(self, target, text: str, font, pos: Tuple[float, float],
             color: Color = WHITE, outline_color: Optional[Color] = OUTLINE,
             outline: int = 2, anchor: str = "center", max_width: Optional[int] = None,
             alpha: int = 255, scale: float = 1.0):
        """Desenha texto. `max_width` encolhe o texto se ele for largo demais."""
        surf = self.render(text, font, color, outline_color, outline)
        if abs(scale - 1.0) > 0.01:
            surf = pygame.transform.smoothscale(
                surf, (max(1, int(surf.get_width() * scale)),
                       max(1, int(surf.get_height() * scale))))
        if max_width is not None and surf.get_width() > max_width:
            ratio = max_width / surf.get_width()
            surf = pygame.transform.smoothscale(
                surf, (max(1, int(surf.get_width() * ratio)),
                       max(1, int(surf.get_height() * ratio))))
        if alpha < 255:
            surf = surf.copy()          # copia para não alterar a imagem em cache
            surf.set_alpha(alpha)
        rect = surf.get_rect(**{anchor: (int(pos[0]), int(pos[1]))})
        target.blit(surf, rect)
        return rect


# =============================================================================
# 7. ENTIDADES
# =============================================================================
class Bird:
    """O pássaro: física (gravidade + pulo), animação e desenho."""

    WING_SEQUENCE = (0, 1, 2, 1)     # ordem dos quadros da animação de asa
    WING_FRAME_TIME = 0.07           # segundos por quadro

    def __init__(self, frames) -> None:
        self.frames = frames
        self.reset()

    def reset(self) -> None:
        self.x = float(BIRD_X)
        self.y = float(BIRD_START_Y)
        self.vy = 0.0                # velocidade vertical (px/s)
        self.angle = 0.0             # inclinação em graus (+ = bico para cima)
        self.anim_clock = 0.0

    def flap(self) -> None:
        """Pulo: define a velocidade para cima (não soma, para o controle ser previsível)."""
        self.vy = FLAP_VELOCITY

    def idle(self, dt: float, t: float) -> None:
        """Flutuação suave usada no menu (sem gravidade)."""
        self.anim_clock += dt
        self.y = BIRD_START_Y + math.sin(t * 5.0) * 7.0
        self.vy = 0.0
        self.angle = math.sin(t * 5.0 + 1.2) * 6.0

    def update(self, dt: float) -> None:
        """Física durante a partida (integração de Euler semi-implícita)."""
        self.anim_clock += dt
        self.vy = min(self.vy + GRAVITY * dt, MAX_FALL_SPEED)
        self.y += self.vy * dt
        if self.y - BIRD_RADIUS < 0:         # teto: não deixa sair da tela
            self.y = float(BIRD_RADIUS)
            self.vy = max(self.vy, 0.0)
        # Inclinação suave: bico sobe ao pular e desce conforme acelera na queda
        target = 28.0 if self.vy < 0 else -min(85.0, self.vy * 0.13)
        self.angle += (target - self.angle) * min(1.0, 14.0 * dt)

    def fall(self, dt: float) -> bool:
        """Queda depois de bater num cano. Retorna True quando toca o chão."""
        self.vy = min(self.vy + GRAVITY * dt, MAX_FALL_SPEED)
        self.y += self.vy * dt
        self.angle = max(-90.0, self.angle - 420.0 * dt)
        if self.y + BIRD_RADIUS >= GROUND_Y:
            self.land()
            return True
        return False

    def land(self) -> None:
        """Coloca o pássaro parado em cima do chão, de bico para baixo."""
        self.y = float(GROUND_Y - BIRD_RADIUS)
        self.vy = 0.0
        self.angle = -90.0

    def draw(self, surface) -> None:
        index = int(self.anim_clock / self.WING_FRAME_TIME) % len(self.WING_SEQUENCE)
        frame_id = self.WING_SEQUENCE[index]
        if self.angle < -55.0:               # mergulhando: asas paradas
            frame_id = 1
        image = pygame.transform.rotozoom(self.frames[frame_id], self.angle, 1.0)
        surface.blit(image, image.get_rect(center=(round(self.x), round(self.y))))


class Pipe:
    """Um par de canos (cima + baixo) com uma abertura no meio."""

    def __init__(self, x: float, center_y: float, gap: float) -> None:
        self.x = float(x)                       # borda esquerda da boca do cano
        self.gap_top = center_y - gap / 2       # onde termina o cano de cima
        self.gap_bottom = center_y + gap / 2    # onde começa o cano de baixo
        self.scored = False                     # já deu ponto?

    @property
    def center_x(self) -> float:
        return self.x + PIPE_CAP_WIDTH / 2

    def rects(self) -> List[Rect4]:
        """Retângulos de colisão: corpo + boca de cada um dos dois canos."""
        x = int(self.x)
        gap_top, gap_bottom = int(self.gap_top), int(self.gap_bottom)
        body_x = x + PIPE_CAP_OVERHANG
        return [
            (body_x, 0, PIPE_WIDTH, gap_top - PIPE_CAP_HEIGHT),                 # corpo de cima
            (x, gap_top - PIPE_CAP_HEIGHT, PIPE_CAP_WIDTH, PIPE_CAP_HEIGHT),    # boca de cima
            (x, gap_bottom, PIPE_CAP_WIDTH, PIPE_CAP_HEIGHT),                   # boca de baixo
            (body_x, gap_bottom + PIPE_CAP_HEIGHT, PIPE_WIDTH,
             GROUND_Y - gap_bottom - PIPE_CAP_HEIGHT),                          # corpo de baixo
        ]


class PipeManager:
    """Gera (proceduralmente), move, remove e desenha os canos."""

    def __init__(self) -> None:
        self.pipes: List[Pipe] = []
        self.last_center = float(BIRD_START_Y)

    def reset(self) -> None:
        self.pipes.clear()
        self.last_center = float(BIRD_START_Y)

    def spawn(self, x: float, gap: float) -> None:
        """
        Cria um novo par de canos.

        A altura da abertura é aleatória, mas limitada a PIPE_MAX_SHIFT de
        distância da anterior: assim a passagem é SEMPRE alcançável.
        """
        lowest = PIPE_MIN_MARGIN + gap / 2                    # limite superior do centro
        highest = GROUND_Y - PIPE_MIN_MARGIN - gap / 2        # limite inferior do centro
        low = max(lowest, self.last_center - PIPE_MAX_SHIFT)
        high = min(highest, self.last_center + PIPE_MAX_SHIFT)
        center = random.uniform(low, high)
        self.last_center = center
        self.pipes.append(Pipe(x, center, gap))

    def update(self, dt: float, speed: float, score: int) -> None:
        for pipe in self.pipes:
            pipe.x -= speed * dt
        # Remove canos que já saíram totalmente pela esquerda
        self.pipes = [p for p in self.pipes if p.x + PIPE_CAP_WIDTH > 0]
        # Cria o próximo cano um pouco fora da tela (sem "aparecer do nada")
        if not self.pipes:
            self.spawn(FIRST_PIPE_X, pipe_gap(score))
        elif self.pipes[-1].x + PIPE_SPACING <= WIDTH + 20:
            self.spawn(self.pipes[-1].x + PIPE_SPACING, pipe_gap(score))

    def draw(self, surface, assets: Assets) -> None:
        for pipe in self.pipes:
            x = int(pipe.x)
            gap_top, gap_bottom = int(pipe.gap_top), int(pipe.gap_bottom)
            body_x = x + PIPE_CAP_OVERHANG
            # Cano de cima: corpo (do teto até a boca) + boca virada para baixo
            top_body_h = gap_top - PIPE_CAP_HEIGHT
            if top_body_h > 0:
                surface.blit(assets.pipe_body, (body_x, 0), (0, 0, PIPE_WIDTH, top_body_h))
            surface.blit(assets.pipe_cap_down, (x, top_body_h))
            # Cano de baixo: boca virada para cima + corpo (até o chão)
            surface.blit(assets.pipe_cap_up, (x, gap_bottom))
            body_y = gap_bottom + PIPE_CAP_HEIGHT
            bottom_body_h = GROUND_Y - body_y
            if bottom_body_h > 0:
                surface.blit(assets.pipe_body, (body_x, body_y), (0, 0, PIPE_WIDTH, bottom_body_h))


class Particle:
    """Partícula simples (penas ao bater, fumacinha ao pular)."""

    __slots__ = ("x", "y", "vx", "vy", "life", "max_life", "color", "size", "gravity")

    def __init__(self, x: float, y: float, vx: float, vy: float, life: float,
                 color: Color, size: float, gravity: float = 900.0) -> None:
        self.x, self.y, self.vx, self.vy = x, y, vx, vy
        self.life = self.max_life = life
        self.color, self.size, self.gravity = color, size, gravity

    def update(self, dt: float) -> bool:
        """Atualiza a partícula. Retorna False quando ela deve desaparecer."""
        self.vy += self.gravity * dt
        self.x += self.vx * dt
        self.y += self.vy * dt
        self.life -= dt
        return self.life > 0

    def draw(self, surface) -> None:
        radius = max(1, int(self.size * self.life / self.max_life))
        pygame.draw.circle(surface, self.color, (int(self.x), int(self.y)), radius)


class Ground:
    """Chão com rolagem infinita."""

    def __init__(self, sprite) -> None:
        self.sprite = sprite
        self.offset = 0.0

    def update(self, dt: float, speed: float) -> None:
        self.offset = (self.offset + speed * dt) % GROUND_PERIOD

    def draw(self, surface) -> None:
        surface.blit(self.sprite, (-int(self.offset), GROUND_Y))


class Cloud:
    def __init__(self, surf, x: float, y: float, speed: float) -> None:
        self.surf, self.x, self.y, self.speed = surf, x, y, speed


class Background:
    """Céu + nuvens + cidade + colinas, com paralaxe (camadas distantes andam mais devagar)."""

    CITY_FACTOR = 0.08     # fração da velocidade do mundo
    HILLS_FACTOR = 0.22

    def __init__(self, assets: Assets) -> None:
        self.assets = assets
        self.city_offset = 0.0
        self.hills_offset = 0.0
        self.clouds = [
            Cloud(random.choice(assets.clouds), random.uniform(-40, WIDTH),
                  random.uniform(40, 300), random.uniform(6, 16))
            for _ in range(6)
        ]

    def update(self, dt: float, world_speed: float) -> None:
        self.city_offset = (self.city_offset + world_speed * self.CITY_FACTOR * dt) % WIDTH
        self.hills_offset = (self.hills_offset + world_speed * self.HILLS_FACTOR * dt) % WIDTH
        for cloud in self.clouds:
            cloud.x -= (cloud.speed + world_speed * 0.04) * dt
            if cloud.x + cloud.surf.get_width() < 0:      # saiu pela esquerda: reaparece à direita
                cloud.surf = random.choice(self.assets.clouds)
                cloud.x = WIDTH + random.uniform(10, 90)
                cloud.y = random.uniform(40, 300)
                cloud.speed = random.uniform(6, 16)

    @staticmethod
    def _draw_layer(surface, layer, offset: float) -> None:
        """Desenha uma camada duas vezes lado a lado para a rolagem nunca ter falhas."""
        x = -(int(offset) % WIDTH)
        y = GROUND_Y - layer.get_height()
        surface.blit(layer, (x, y))
        surface.blit(layer, (x + WIDTH, y))

    def draw(self, surface) -> None:
        surface.blit(self.assets.sky, (0, 0))
        for cloud in self.clouds:
            surface.blit(cloud.surf, (int(cloud.x), int(cloud.y)))
        self._draw_layer(surface, self.assets.city, self.city_offset)
        self._draw_layer(surface, self.assets.hills, self.hills_offset)


# =============================================================================
# 8. JOGO (máquina de estados + laço principal)
# =============================================================================
class Game:
    FLAP_KEYS = (pygame.K_SPACE, pygame.K_UP, pygame.K_w)

    def __init__(self) -> None:
        # O mixer precisa ser configurado ANTES do pygame.init()
        pygame.mixer.pre_init(SAMPLE_RATE, -16, 1, 512)
        pygame.init()
        pygame.display.set_caption(TITLE)
        self.screen = self._create_window()
        self.canvas = pygame.Surface((WIDTH, HEIGHT)).convert()
        self.clock = pygame.time.Clock()
        self._viewport = pygame.Rect(0, 0, *self.screen.get_size())
        self._last_action_ms = -1000
        self._update_viewport()

        self.assets = Assets()
        try:
            pygame.display.set_icon(self.assets.bird_frames[1])
        except pygame.error:
            pass
        self.text = TextRenderer()
        self.sound = SoundManager()
        self.highscore = HighScore()

        self.bird = Bird(self.assets.bird_frames)
        self.pipes = PipeManager()
        self.ground = Ground(self.assets.ground)
        self.background = Background(self.assets)
        self.particles: List[Particle] = []

        # Camadas de efeito reutilizáveis
        self.dim = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        self.dim.fill((0, 0, 0, 140))
        self.flash_surface = pygame.Surface((WIDTH, HEIGHT))
        self.flash_surface.fill(WHITE)

        self.running = True
        self.state = State.MENU
        self.score = 0
        self.new_record = False
        self.clock_time = 0.0        # tempo total (usado em animações de interface)
        self.over_timer = 0.0        # tempo desde o game over
        self.resume_timer = 0.0      # contagem regressiva ao sair da pausa
        self.shake_timer = 0.0
        self.flash = 0.0
        self.score_pop = 0.0
        self.die_sound_delay = 0.0

    @staticmethod
    def _create_window():
        """Cria uma janela adaptada para desktop e dispositivos móveis."""
        is_android = hasattr(pygame, "ANDROID") and pygame.ANDROID
        if is_android:
            try:
                return pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
            except (pygame.error, AttributeError):
                pass

        try:
            display = pygame.display.Info()
            if display.current_w > 0 and display.current_h > 0:
                mobile_ratio = min(display.current_w, display.current_h) < 900
                if mobile_ratio:
                    return pygame.display.set_mode(
                        (display.current_w, display.current_h),
                        pygame.FULLSCREEN | pygame.SCALED,
                    )
        except pygame.error:
            pass

        try:
            return pygame.display.set_mode((WIDTH, HEIGHT), pygame.SCALED | pygame.RESIZABLE)
        except (pygame.error, AttributeError):
            return pygame.display.set_mode((WIDTH, HEIGHT))

    def _update_viewport(self) -> None:
        """Mantém o jogo em 400x640, centralizado e sem distorcer a imagem."""
        screen_w, screen_h = self.screen.get_size()
        scale = min(screen_w / WIDTH, screen_h / HEIGHT)
        scaled_w = max(1, int(WIDTH * scale))
        scaled_h = max(1, int(HEIGHT * scale))
        self._viewport = pygame.Rect(
            (screen_w - scaled_w) // 2,
            (screen_h - scaled_h) // 2,
            scaled_w,
            scaled_h,
        )

    # ------------------------------------------------------------------ transições
    def go_to_menu(self) -> None:
        self.bird.reset()
        self.pipes.reset()
        self.particles.clear()
        self.score = 0
        self.new_record = False
        self.resume_timer = 0.0
        self.state = State.MENU

    def start_game(self) -> None:
        """Começa (ou reinicia) uma partida já com o primeiro pulo."""
        self.bird.reset()
        self.pipes.reset()
        self.particles.clear()
        self.score = 0
        self.new_record = False
        self.resume_timer = 0.0
        self.state = State.PLAYING
        self.flap()

    def flap(self) -> None:
        self.bird.flap()
        self.sound.play("flap")
        for _ in range(3):   # fumacinha atrás do pássaro
            self.particles.append(Particle(
                self.bird.x - 12, self.bird.y + 6,
                random.uniform(-90, -40), random.uniform(0, 50),
                0.28, WHITE, 4.0, gravity=0.0))

    def pause(self) -> None:
        if self.state is State.PLAYING:
            self.state = State.PAUSED

    def resume(self) -> None:
        if self.state is State.PAUSED:
            self.resume_timer = RESUME_COUNTDOWN      # dá tempo de se preparar
            self.state = State.PLAYING

    def die(self, cause: str) -> None:
        """Chamado no instante da colisão. `cause` é "ground" ou "pipe"."""
        if self.state is not State.PLAYING:
            return
        self.state = State.DYING
        self.new_record = self.highscore.submit(self.score)
        self.sound.play("hit")
        self.shake_timer = SHAKE_TIME
        self.flash = 0.85
        for _ in range(14):   # explosão de penas
            self.particles.append(Particle(
                self.bird.x, self.bird.y,
                random.uniform(-180, 180), random.uniform(-260, 40),
                random.uniform(0.4, 0.8),
                random.choice(((250, 205, 50), (255, 238, 140), WHITE)),
                random.uniform(3, 6)))
        if cause == "ground":
            self.bird.land()
            self._enter_game_over()
        else:
            self.bird.vy = max(self.bird.vy, 0.0)     # cancela a subida e começa a cair
            self.die_sound_delay = 0.2

    def _enter_game_over(self) -> None:
        self.state = State.GAME_OVER
        self.over_timer = 0.0

    # ------------------------------------------------------------------ entrada
    def handle_events(self) -> None:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                self.running = False
            elif event.type == pygame.KEYDOWN:
                self._on_key(event.key)
            elif event.type == pygame.MOUSEBUTTONDOWN:
                # Ignora o clique "falso" que alguns sistemas geram junto com o toque
                if event.button == 1 and not getattr(event, "touch", False):
                    self._trigger_action()
            elif event.type == FINGERDOWN:
                self._trigger_action()
            elif event.type == getattr(pygame, "WINDOWRESIZED", -3):
                self.screen = pygame.display.set_mode(
                    event.size,
                    pygame.SCALED | pygame.RESIZABLE,
                )
                self._update_viewport()
            elif event.type == WINDOWFOCUSLOST:
                self.pause()    # perdeu o foco da janela: pausa sozinho

        app_will_enter_background = getattr(pygame, "APP_WILLENTERBACKGROUND", None)
        if app_will_enter_background is not None:
            for event in pygame.event.get(app_will_enter_background):
                self.pause()

    def _trigger_action(self) -> None:
        """Evita dois pulos quando toque gera eventos de toque e mouse juntos."""
        now = pygame.time.get_ticks()
        if now - self._last_action_ms >= 50:
            self._last_action_ms = now
            self._on_action()

    def _on_key(self, key: int) -> None:
        if key == pygame.K_m:
            self.sound.toggle_mute()
        elif key == pygame.K_F11:
            try:
                pygame.display.toggle_fullscreen()
                self._update_viewport()
            except pygame.error:
                pass
        elif key in self.FLAP_KEYS:
            self._trigger_action()
        elif key in (pygame.K_RETURN, pygame.K_KP_ENTER):
            if self.state in (State.MENU, State.GAME_OVER):
                self._trigger_action()
        elif key == pygame.K_r:
            if self.state is State.GAME_OVER:
                self._trigger_action()
        elif key == pygame.K_p:
            if self.state is State.PLAYING:
                self.pause()
            elif self.state is State.PAUSED:
                self.resume()
        elif key == pygame.K_ESCAPE:
            if self.state is State.MENU:
                self.running = False
            elif self.state is State.PLAYING:
                self.pause()
            elif self.state is State.PAUSED:
                self.resume()
            elif self.state is State.GAME_OVER:
                self.go_to_menu()

    def _on_action(self) -> None:
        """Ação principal (espaço / clique / toque): depende do estado atual."""
        if self.state is State.MENU:
            self.start_game()
        elif self.state is State.PLAYING:
            if self.resume_timer <= 0:      # durante a contagem, o pulo é ignorado
                self.flap()
        elif self.state is State.PAUSED:
            self.resume()
        elif self.state is State.GAME_OVER:
            if self.over_timer >= RESTART_DELAY:
                self.start_game()

    # ------------------------------------------------------------------ atualização
    def update(self, dt: float) -> None:
        self.clock_time += dt
        if self.state is State.PAUSED:
            return

        self.shake_timer = max(0.0, self.shake_timer - dt)
        self.flash = max(0.0, self.flash - dt / FLASH_TIME)
        self.score_pop = max(0.0, self.score_pop - dt)
        self.particles = [p for p in self.particles if p.update(dt)]

        if self.state is State.MENU:
            self.background.update(dt, BASE_SPEED)
            self.ground.update(dt, BASE_SPEED)
            self.bird.idle(dt, self.clock_time)
        elif self.state is State.PLAYING:
            self._update_playing(dt)
        elif self.state is State.DYING:
            self._update_dying(dt)
        elif self.state is State.GAME_OVER:
            self.over_timer += dt

    def _update_playing(self, dt: float) -> None:
        if self.resume_timer > 0:           # contagem após a pausa: mundo congelado
            self.resume_timer -= dt
            return

        speed = pipe_speed(self.score)
        self.background.update(dt, speed)
        self.ground.update(dt, speed)
        self.bird.update(dt)
        self.pipes.update(dt, speed, self.score)

        cause = self._check_collision()
        if cause is not None:
            self.die(cause)
            return
        self._update_score()

    def _update_dying(self, dt: float) -> None:
        if self.die_sound_delay > 0:
            self.die_sound_delay -= dt
            if self.die_sound_delay <= 0:
                self.sound.play("die")
        if self.bird.fall(dt):
            self._enter_game_over()

    def _check_collision(self) -> Optional[str]:
        """Retorna "ground", "pipe" ou None."""
        if self.bird.y + BIRD_RADIUS >= GROUND_Y:
            return "ground"
        for pipe in self.pipes.pipes:
            # Só vale a pena testar canos que estão perto do pássaro
            if pipe.x > self.bird.x + BIRD_RADIUS or pipe.x + PIPE_CAP_WIDTH < self.bird.x - BIRD_RADIUS:
                continue
            for rect in pipe.rects():
                if circle_rect_collision(self.bird.x, self.bird.y, BIRD_RADIUS, rect):
                    return "pipe"
        return None

    def _update_score(self) -> None:
        """Dá 1 ponto quando o pássaro ultrapassa o centro de um cano."""
        for pipe in self.pipes.pipes:
            if not pipe.scored and pipe.center_x < self.bird.x:
                pipe.scored = True
                self.score += 1
                self.score_pop = SCORE_POP_TIME
                self.sound.play("point")

    # ------------------------------------------------------------------ desenho
    def draw(self) -> None:
        canvas = self.canvas
        self.background.draw(canvas)
        self.pipes.draw(canvas, self.assets)
        self.ground.draw(canvas)
        for particle in self.particles:
            particle.draw(canvas)
        self.bird.draw(canvas)

        if self.state is State.MENU:
            self._draw_menu(canvas)
        elif self.state is State.GAME_OVER:
            self._draw_game_over(canvas)
        else:
            self._draw_score(canvas)
            if self.state is State.PAUSED:
                self._draw_pause(canvas)
            elif self.state is State.PLAYING and self.resume_timer > 0:
                self._draw_countdown(canvas)

        # Tremor de tela ao bater
        offset = (0, 0)
        if self.shake_timer > 0:
            magnitude = max(1, int(7 * self.shake_timer / SHAKE_TIME))
            offset = (random.randint(-magnitude, magnitude),
                      random.randint(-magnitude, magnitude))
        self.screen.fill((0, 0, 0))

        if self._viewport.size == (WIDTH, HEIGHT):
            destination = (self._viewport.x + offset[0], self._viewport.y + offset[1])
            self.screen.blit(canvas, destination)
        else:
            scaled = pygame.transform.smoothscale(canvas, self._viewport.size)
            destination = (self._viewport.x + offset[0], self._viewport.y + offset[1])
            self.screen.blit(scaled, destination)

        # Clarão branco ao bater
        if self.flash > 0:
            self.flash_surface.set_alpha(int(255 * self.flash))
            flash_scaled = pygame.transform.smoothscale(
                self.flash_surface,
                self._viewport.size,
            )
            self.screen.blit(flash_scaled, self._viewport)
        pygame.display.flip()

    def _draw_score(self, surface) -> None:
        scale = 1.0 + 0.35 * (self.score_pop / SCORE_POP_TIME)   # "pulinho" ao pontuar
        self.text.draw(surface, str(self.score), self.assets.fonts.score,
                       (WIDTH // 2, 85), WHITE, OUTLINE, 4, scale=scale)

    def _draw_menu(self, surface) -> None:
        fonts, text = self.assets.fonts, self.text
        text.draw(surface, "FLAPPY PY", fonts.title, (WIDTH // 2, 135),
                  YELLOW, OUTLINE, 4, max_width=WIDTH - 40)
        text.draw(surface, "um clássico feito em Python", fonts.small,
                  (WIDTH // 2, 183), WHITE, OUTLINE, 2)
        pulse = int(170 + 85 * math.sin(self.clock_time * 4.0))
        text.draw(surface, "TOQUE OU PRESSIONE ESPAÇO", fonts.body, (WIDTH // 2, 385),
                  WHITE, OUTLINE, 2, max_width=WIDTH - 30, alpha=pulse)
        if self.highscore.best > 0:
            text.draw(surface, f"Recorde: {self.highscore.best}", fonts.heading,
                      (WIDTH // 2, 440), YELLOW, OUTLINE, 3)
        # Dicas de controles sobre o chão
        text.draw(surface, "TOQUE / ESPAÇO / CLIQUE: pular", fonts.small,
                  (WIDTH // 2, GROUND_Y + 40), OUTLINE, None, max_width=WIDTH - 20)
        text.draw(surface, "P/ESC: pausar   |   M: som   |   F11: tela cheia", fonts.small,
                  (WIDTH // 2, GROUND_Y + 66), OUTLINE, None, max_width=WIDTH - 20)

    def _draw_pause(self, surface) -> None:
        fonts, text = self.assets.fonts, self.text
        surface.blit(self.dim, (0, 0))
        text.draw(surface, "PAUSADO", fonts.title, (WIDTH // 2, 270),
                  YELLOW, OUTLINE, 4, max_width=WIDTH - 40)
        text.draw(surface, "Toque ou pressione P / ESPAÇO", fonts.body, (WIDTH // 2, 335),
                  WHITE, OUTLINE, 2, max_width=WIDTH - 30)
        text.draw(surface, "para continuar", fonts.body, (WIDTH // 2, 365),
                  WHITE, OUTLINE, 2, max_width=WIDTH - 30)

    def _draw_countdown(self, surface) -> None:
        number = max(1, int(math.ceil(self.resume_timer / (RESUME_COUNTDOWN / 3))))
        self.text.draw(surface, str(number), self.assets.fonts.title,
                       (WIDTH // 2, 270), WHITE, OUTLINE, 4)

    def _draw_medal(self, surface, center: Tuple[int, int], radius: int) -> None:
        medal = medal_for(self.score)
        if medal is None:       # sem medalha: encaixe vazio
            pygame.draw.circle(surface, (196, 186, 132), center, radius)
            pygame.draw.circle(surface, OUTLINE, center, radius, 3)
            return
        _, _, base, light = medal
        pygame.draw.circle(surface, OUTLINE, center, radius)
        pygame.draw.circle(surface, base, center, radius - 3)
        pygame.draw.circle(surface, light, center, radius - 11, 3)
        pygame.draw.circle(surface, light, (center[0] - radius // 3, center[1] - radius // 3), 5)

    def _draw_game_over(self, surface) -> None:
        fonts, text = self.assets.fonts, self.text
        ease = ease_out_cubic(self.over_timer / PANEL_SLIDE_TIME)

        # Título desce de cima e o painel sobe de baixo
        text.draw(surface, "FIM DE JOGO", fonts.title, (WIDTH // 2, int(125 - (1 - ease) * 220)),
                  YELLOW, OUTLINE, 4, max_width=WIDTH - 40)

        panel_w, panel_h = 320, 220
        px = (WIDTH - panel_w) // 2
        py = int(190 + (1 - ease) * 460)
        rounded_rect(surface, OUTLINE, (px, py, panel_w, panel_h), 16)
        rounded_rect(surface, PANEL_BG, (px + 4, py + 4, panel_w - 8, panel_h - 8), 13)

        # Coluna esquerda: medalha
        self._draw_medal(surface, (px + 72, py + 108), 38)
        medal = medal_for(self.score)
        text.draw(surface, medal[1] if medal else "Sem medalha", fonts.small,
                  (px + 72, py + 168), OUTLINE, None, max_width=130)

        # Coluna direita: pontuação e recorde
        col_x = px + 222
        text.draw(surface, "PONTOS", fonts.small, (col_x, py + 40), ORANGE, None)
        text.draw(surface, str(self.score), fonts.heading, (col_x, py + 78), WHITE, OUTLINE, 3)
        text.draw(surface, "RECORDE", fonts.small, (col_x, py + 128), ORANGE, None)
        text.draw(surface, str(self.highscore.best), fonts.heading, (col_x, py + 166),
                  WHITE, OUTLINE, 3)
        if self.new_record:
            badge = pygame.Rect(0, 0, 54, 22)
            badge.center = (px + panel_w - 40, py + 128)
            rounded_rect(surface, RED, badge, 8)
            text.draw(surface, "NOVO!", fonts.small, badge.center, WHITE, None)

        # Instruções (aparecem depois do pequeno bloqueio anti-clique acidental)
        if self.over_timer >= RESTART_DELAY:
            pulse = int(190 + 65 * math.sin(self.clock_time * 5.0))
            text.draw(surface, "TOQUE / ESPAÇO / CLIQUE: jogar de novo", fonts.body,
                      (WIDTH // 2, py + panel_h + 36), WHITE, OUTLINE, 2,
                      max_width=WIDTH - 30, alpha=pulse)
            text.draw(surface, "ESC: voltar ao menu", fonts.small,
                      (WIDTH // 2, py + panel_h + 68), WHITE, OUTLINE, 2)

    # ------------------------------------------------------------------ laço principal
    async def run(self) -> None:
        while self.running:
            dt = min(self.clock.tick(FPS) / 1000.0, MAX_DT)
            self.handle_events()
            self.update(dt)
            self.draw()
            await asyncio.sleep(0)


async def main() -> None:
    game = Game()
    try:
        await game.run()
    finally:
        pygame.quit()


if __name__ == "__main__":
    asyncio.run(main())
