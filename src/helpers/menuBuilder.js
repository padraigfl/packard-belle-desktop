const buildCustomOptions = rows =>
  Object.keys(rows).reduce(
    (acc, val) => [
      ...acc,
      {
        title: val,
        options: rows[val]
      }
    ],
    []
  );

export const buildMenu = (props, customOptions = {}) => {
  const onClose = [{ title: "Close", onClick: () => props.onClose(props) }];
  const saveOptions =
    props.onSave || props.onSaveAs
      ? [
          { title: "Save As...", onClick: data => props.onSaveAs(props, data) },
          {
            title: "Save",
            onClick: props.onSave && (data => props.onSave(props, data)),
            isDisabled: props.readOnly || !props.onSave
          }
        ]
      : [];
  const multiInstance = props.multiInstance
    ? [
        {
          title: "Open",
          isDisabled: !props.onOpenSearch,
          onClick: props.onOpenSearch
        },
        {
          title: "New",
          onClick: () => props.onOpen(props, { new: true }),
          isDisabled: props.singleInstance
        }
      ]
    : [];
  if (props.multiWindow) {
    onClose.push([{ title: "Exit", onClick: () => props.onExit(props) }]);
  }
  const customElements = buildCustomOptions(customOptions);
  return [
    {
      title: "File",
      options: [...multiInstance, ...saveOptions, ...onClose]
    },
    ...customElements,
    {
      title: "Help",
      options: [
        [{ title: "Help Topics", isDisabled: true }],
        { title: `About ${props.title}`, isDisabled: true }
      ]
    }
  ];
};

export default buildMenu;
