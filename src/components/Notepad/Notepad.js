import React from "react";
import Window from "../tools/Window";
import cx from "classnames";
import { notepad16 } from "../../icons";
import "./_styles.scss";
import { WindowProgram } from "packard-belle";

export const buildMenu = (props, state) => [
  {
    title: "File",
    options: [
      {
        title: "New",
        isDisabled: !props.multiWindow && !props.onOpen,
        onClick: () => props.onOpen(props.id)
      },
      {
        title: "Open",
        isDisabled: true,
        onClick: () => props.onOpen(props.id)
      },
      { title: "Close", onClick: () => props.onClose(props.id) },
      {
        title: "Wrap",
        onClick: () => state.toggleWrap(!state.wrap),
        isChecked: state.wrap
      }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const Notepad = props => {
  const [wrap, toggleWrap] = React.useState(false);
  const [text, setText] = React.useState(props.data.content || "");

  return (
    <Window
      {...props}
      icon={notepad16}
      footer={[
        { text: "needs 100% width height" },
        { text: "overflow control" }
      ]}
      menuOptions={buildMenu(props, { toggleWrap, wrap })}
      className={cx("Notepad", props.className, {
        "Notepad--wrap": wrap
      })}
      title={`${
        props.title !== "Notepad" ? props.title : "Untitled"
      } - Notepad`}
      Component={WindowProgram}
    >
      <div className="Notepad__textarea">
        <textarea onChange={e => setText(e.target.value)}>{text}</textarea>
      </div>
    </Window>
  );
};

Notepad.defaultProps = {
  data: {
    content: ""
  }
};

export default Notepad;
