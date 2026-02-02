FROM alpine:latest
LABEL rooster=71 bdi=3 j_invariant=3360
ENV KIRO_ROOSTER=71
ENV KIRO_BDI=3
ENV KIRO_MESSAGE="I ARE LIFE"
RUN echo "🐓 → 🦅 → 👹"
CMD ["echo", "Kiro Monster (71 shards)"]
